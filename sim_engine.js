// Slate IQ - NFL single-game simulator (drive-level Monte Carlo). Load before app code.
// Pure engine: no page access. index.html builds the inputs and draws the results.
//
// How one simulated game works (each team, independently except for a shared pace shock):
//   1. Drives: ~11 per team, nudged by a game-wide pace shock (fast games give both teams more).
//   2. Each drive ends TD / FG / nothing. Rates are scaled so the average score equals the
//      team's implied total, then shocked per sim (good day / bad day) so scores spread out.
//   3. Game script: the final margin tilts volume - trailing teams throw more, leaders run more.
//   4. Volume -> players: targets and carries are handed out one at a time by each player's
//      usage share (Slate IQ Model game logs); catches, yards per catch/carry are drawn per play.
//      The same good-day shock that raised the team's scoring also raises its yardage, which is
//      what makes QB + pass catchers (and bring-backs, via the shared pace) move together.
//   5. TDs: each team TD is a pass or a rush, then goes to a player by TD-share.
//   6. Calibration: every player's simulated average is scaled to his Slate IQ projection
//      (whatever Projection Source is selected), so the sim keeps the market's averages and
//      only adds the shape: ceilings, TD odds, and which outcomes happen together.
(function(root){
  'use strict';

  var LG = { drives: 11, tdRate: 0.23, fgRate: 0.16, ptsPerTd: 6.94, xp: 0.94,
             tgtPerAtt: 0.90, teamCarries: 26, qShock: 0.18, paceShock: 0.06, script: 0.015 };

  // Seeded RNG so the same inputs give the same results every run.
  function rng(seed){
    var a = seed >>> 0;
    var spare = null;
    function u(){ a |= 0; a = a + 0x6D2B79F5 | 0; var t = Math.imul(a ^ a >>> 15, 1 | a);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }
    function n(){ // standard normal
      if (spare !== null){ var s = spare; spare = null; return s; }
      var x, y, r; do { x = 2 * u() - 1; y = 2 * u() - 1; r = x * x + y * y; } while (!r || r >= 1);
      var f = Math.sqrt(-2 * Math.log(r) / r); spare = y * f; return x * f;
    }
    function pois(l){ if (l <= 0) return 0; var L = Math.exp(-l), k = 0, p = 1; do { k++; p *= u(); } while (p > L); return k - 1; }
    return { u: u, n: n, pois: pois };
  }

  function clamp(x, lo, hi){ return x < lo ? lo : x > hi ? hi : x; }

  // Picks an index from cumulative weights.
  function pick(cum, total, r){
    var x = r * total;
    for (var i = 0; i < cum.length; i++) if (x < cum[i]) return i;
    return cum.length - 1;
  }
  function cumulative(ws){ var c = [], s = 0; ws.forEach(function(w){ s += Math.max(0, w); c.push(s); }); return { cum: c, total: s }; }

  // Prepares one team: usage shares and an "other" bucket for players not in the pool.
  function prepTeam(t){
    var P = t.players;
    var qb = P.filter(function(p){ return p.pos === 'QB'; }).sort(function(a, b){ return (b.at || 0) - (a.at || 0); })[0] || null;
    var baseAtt = qb && qb.at ? qb.at : 33;
    var recv = P.filter(function(p){ return p.pos !== 'QB' && p.pos !== 'DEF' && p.pos !== 'K' && p.tg > 0; });
    var rush = P.filter(function(p){ return p.pos !== 'DEF' && p.pos !== 'K' && p.ca > 0; });
    var tgtTeam = baseAtt * LG.tgtPerAtt;
    var tgSum = recv.reduce(function(s, p){ return s + p.tg; }, 0);
    var caSum = rush.reduce(function(s, p){ return s + p.ca; }, 0);
    var otherTg = Math.max(0, tgtTeam - tgSum), otherCa = Math.max(0, LG.teamCarries - caSum);
    var tgW = recv.map(function(p){ return p.tg; }).concat([otherTg]);
    var caW = rush.map(function(p){ return p.ca; }).concat([otherCa]);
    var tdRecW = recv.map(function(p){ return p.tg * p.tdt; }).concat([otherTg * 0.045]);
    var tdRushW = rush.map(function(p){ return p.ca * p.tdc; }).concat([otherCa * 0.035]);
    var passTdExp = baseAtt * (qb && qb.tda ? qb.tda : 0.043);
    var rushTdExp = rush.reduce(function(s, p){ return s + p.ca * p.tdc; }, 0) + otherCa * 0.035;
    return {
      t: t, qb: qb, baseAtt: baseAtt, baseCar: caSum + otherCa,
      recv: recv, rush: rush,
      tg: cumulative(tgW), ca: cumulative(caW), tdRec: cumulative(tdRecW), tdRush: cumulative(tdRushW),
      passShare: passTdExp / (passTdExp + rushTdExp || 1),
      scale: t.implied / (LG.drives * (LG.tdRate * LG.ptsPerTd + LG.fgRate * 3))
    };
  }

  // input: { away:{team, implied, players:[...]}, home:{...}, sims, seed, scoring:{rec, bonus, fumble} }
  // player: { id, name, pos, salary, target, tg, ca, at, cr, ypt, tdt, ypc, tdc, tda, inta }
  function simulateGame(input){
    // Pilot pass: a quick 2,000-sim run to see how far each player's raw sim average is from
    // his projection, then scale his yards-per-opportunity and TD rate by that gap before the
    // real run. That way TD % and bonus % line up with the projection, not just the average.
    if (!input._calibrated){
      var pilot = simulateGame(Object.assign({}, input, { sims: 2000, _calibrated: true }));
      var gap = {};
      pilot.players.forEach(function(o){ gap[o.id] = o.target > 0 && o.rawMean > 0.5 ? clamp(o.target / o.rawMean, 0.5, 1.8) : 1; });
      var adj = function(t){
        return Object.assign({}, t, { players: t.players.map(function(p){
          if (p.pos === 'QB' || p.pos === 'DEF' || p.pos === 'K') return p;
          var f = gap[p.id];
          return Object.assign({}, p, { ypt: p.ypt * f, ypc: p.ypc * f, tdt: p.tdt * f, tdc: p.tdc * f });
        }) });
      };
      return simulateGame(Object.assign({}, input, { away: adj(input.away), home: adj(input.home), _calibrated: true }));
    }
    var N = input.sims || 10000, R = rng(input.seed || 12345);
    var sc = Object.assign({ rec: 0.5, bonus: true, fumble: -2 }, input.scoring || {});
    var teams = [prepTeam(input.away), prepTeam(input.home)];
    var all = input.away.players.concat(input.home.players);
    var np = all.length;
    var idx = {}; all.forEach(function(p, i){ idx[p.id] = i; });

    var fp = new Float32Array(np * N);         // fantasy points, player-major: fp[i*N + s]
    var td = new Uint8Array(np * N);           // rush+rec TDs
    var bonus = new Uint8Array(np * N);        // hit any yardage bonus
    var scores = [new Uint8Array(N), new Uint8Array(N)];

    // per-sim scratch (stats per player)
    var passY = new Float64Array(np), passTD = new Float64Array(np), ints = new Float64Array(np),
        rushY = new Float64Array(np), recY = new Float64Array(np), rec = new Float64Array(np),
        tds = new Float64Array(np), fum = new Float64Array(np);

    for (var s = 0; s < N; s++){
      passY.fill(0); passTD.fill(0); ints.fill(0); rushY.fill(0); recY.fill(0); rec.fill(0); tds.fill(0); fum.fill(0);
      var pace = Math.exp(R.n() * LG.paceShock);
      var T = [], k;
      // 1-2. Drives and scoring
      for (k = 0; k < 2; k++){
        var tm = teams[k];
        var q = R.n() * LG.qShock;
        var mult = Math.exp(q - LG.qShock * LG.qShock / 2);
        var drives = clamp(Math.round(LG.drives * pace + R.n() * 0.7), 8, 15);
        var pTD = clamp(LG.tdRate * tm.scale * mult, 0.02, 0.75), pFG = clamp(LG.fgRate * tm.scale * mult, 0.02, 0.4);
        var nTD = 0, nFG = 0, xps = 0, pts = 0;
        for (var d = 0; d < drives; d++){
          var r = R.u();
          if (r < pTD){ nTD++; var xp = R.u() < LG.xp ? 1 : 0; xps += xp; pts += 6 + xp; }
          else if (r < pTD + pFG){ nFG++; pts += 3; }
        }
        T.push({ q: q, drives: drives, nTD: nTD, nFG: nFG, xps: xps, pts: pts });
      }
      scores[0][s] = Math.min(255, T[0].pts); scores[1][s] = Math.min(255, T[1].pts);

      // 3-5. Volume, yardage, touchdowns
      for (k = 0; k < 2; k++){
        tm = teams[k]; var me = T[k], opp = T[1 - k];
        var margin = me.pts - opp.pts, vol = me.drives / LG.drives;
        var eff = Math.exp(0.45 * me.q);
        var att = Math.max(10, Math.round(tm.baseAtt * vol * clamp(Math.exp(-LG.script * margin), 0.75, 1.35) * Math.exp(R.n() * 0.08)));
        var car = Math.max(8, Math.round(tm.baseCar * vol * clamp(Math.exp(LG.script * margin), 0.7, 1.35) * Math.exp(R.n() * 0.08)));
        me.att = att;
        var teamPassY = 0;
        var nTg = Math.round(att * LG.tgtPerAtt), i, j, p, y;
        for (j = 0; j < nTg; j++){
          var w = pick(tm.tg.cum, tm.tg.total, R.u());
          if (w >= tm.recv.length){ if (R.u() < 0.64){ y = Math.round(11.5 * eff * Math.exp(0.75 * R.n() - 0.28)); teamPassY += y; } continue; }
          p = tm.recv[w]; i = idx[p.id];
          if (R.u() < Math.min(0.92, p.cr)){
            y = Math.round((p.ypt / p.cr) * eff * Math.exp(0.75 * R.n() - 0.28));
            rec[i]++; recY[i] += y; teamPassY += y;
            if (R.u() < 0.008) fum[i]++;
          }
        }
        for (j = 0; j < car; j++){
          w = pick(tm.ca.cum, tm.ca.total, R.u());
          y = Math.round(-2 + ((w < tm.rush.length ? tm.rush[w].ypc : 4.3) * eff + 2) * Math.exp(0.9 * R.n() - 0.405));
          if (w < tm.rush.length){ i = idx[tm.rush[w].id]; rushY[i] += y; if (R.u() < 0.004) fum[i]++; }
        }
        for (j = 0; j < me.nTD; j++){
          if (R.u() < tm.passShare){
            w = pick(tm.tdRec.cum, tm.tdRec.total, R.u());
            y = Math.round(12 * Math.exp(0.6 * R.n() - 0.18));
            teamPassY += y;
            if (w < tm.recv.length){ i = idx[tm.recv[w].id]; tds[i]++; rec[i]++; recY[i] += y; }
            if (tm.qb) passTD[idx[tm.qb.id]]++;
          } else {
            w = pick(tm.tdRush.cum, tm.tdRush.total, R.u());
            if (w < tm.rush.length){ i = idx[tm.rush[w].id]; tds[i]++; }
          }
        }
        if (tm.qb){
          i = idx[tm.qb.id]; passY[i] = teamPassY;
          var ia = tm.qb.inta || 0.0225; for (j = 0; j < att; j++) if (R.u() < ia) ints[i]++;
        }
        me.ints = tm.qb ? ints[idx[tm.qb.id]] : R.pois(att * 0.0225);
      }

      // Scoring
      for (k = 0; k < 2; k++){
        tm = teams[k]; me = T[k]; opp = T[1 - k];
        tm.t.players.forEach(function(p){
          var i = idx[p.id], f = 0, b = 0;
          if (p.pos === 'DEF'){
            var pa = opp.pts;
            var tier = pa === 0 ? 10 : pa <= 6 ? 7 : pa <= 13 ? 4 : pa <= 20 ? 1 : pa <= 27 ? 0 : pa <= 34 ? -1 : -4;
            var sacks = R.pois(2.3 * (opp.att || 34) / 34), fr = R.pois(0.55), dtd = R.pois(0.03 + 0.06 * (opp.ints + fr));
            f = tier + sacks + 2 * opp.ints + 2 * fr + 6 * dtd;
            tds[i] = dtd;
          } else if (p.pos === 'K'){
            for (var g = 0; g < me.nFG; g++){ var r2 = R.u(); f += r2 < 0.5 ? 3 : r2 < 0.82 ? 4 : 5; }
            f += me.xps;
          } else {
            f = 0.04 * passY[i] + 4 * passTD[i] - ints[i] + 0.1 * (rushY[i] + recY[i]) + sc.rec * rec[i] + 6 * tds[i] + sc.fumble * fum[i];
            if (sc.bonus){
              if (passY[i] >= 300){ f += 3; b = 1; }
              if (rushY[i] >= 100){ f += 3; b = 1; }
              if (recY[i] >= 100){ f += 3; b = 1; }
            }
          }
          fp[i * N + s] = f; td[i * N + s] = Math.min(255, tds[i]); bonus[i * N + s] = b;
        });
      }
    }

    // 6. Calibrate each player's average to his projection, then summarize.
    var out = all.map(function(p, i){
      var off = i * N, sum = 0, s2;
      for (s2 = 0; s2 < N; s2++) sum += fp[off + s2];
      var raw = sum / N;
      var f = p.target > 0 && raw > 0.5 ? clamp(p.target / raw, 0.4, 2.5) : 1;
      for (s2 = 0; s2 < N; s2++) fp[off + s2] *= f;
      var tdHit = 0, bHit = 0;
      for (s2 = 0; s2 < N; s2++){ if (td[off + s2] > 0) tdHit++; if (bonus[off + s2]) bHit++; }
      var sorted = Array.prototype.slice.call(fp.subarray(off, off + N)).sort(function(a, b){ return a - b; });
      return { id: p.id, name: p.name, pos: p.pos, team: p.team, salary: p.salary, target: p.target,
               rawMean: raw, calib: f, mean: raw * f, p25: sorted[Math.floor(N * 0.25)], p50: sorted[Math.floor(N * 0.5)], p90: sorted[Math.floor(N * 0.9)],
               pTD: tdHit / N, pBonus: bHit / N, top1: 0, topK: 0, valueHit: 0 };
    });

    // How often each player is the game's top scorer, and in its top K (K = 6 for FD Single Game).
    var K = Math.min(input.topK || 6, np), order = all.map(function(_, i){ return i; });
    for (s = 0; s < N; s++){
      order.sort(function(a, b){ return fp[b * N + s] - fp[a * N + s]; });
      out[order[0]].top1++;
      for (var t2 = 0; t2 < K; t2++) out[order[t2]].topK++;
    }
    var vm = input.valueMult || 2;
    out.forEach(function(o, i){
      o.top1 /= N; o.topK /= N;
      if (o.salary > 0){ var bar = o.salary / 1000 * vm, h = 0; for (var s3 = 0; s3 < N; s3++) if (fp[i * N + s3] >= bar) h++; o.valueHit = h / N; o.valueBar = bar; }
    });

    var aS = 0, hS = 0, aW = 0, tie = 0, over = 0, mt = input.marketTotal;
    for (s = 0; s < N; s++){
      aS += scores[0][s]; hS += scores[1][s];
      if (scores[0][s] > scores[1][s]) aW++; else if (scores[0][s] === scores[1][s]) tie++;
      if (mt != null && scores[0][s] + scores[1][s] > mt) over++;
    }
    return {
      sims: N, players: out, fp: fp, index: idx, scores: scores,
      game: { away: input.away.team, home: input.home.team, awayImplied: input.away.implied, homeImplied: input.home.implied,
              awayMean: aS / N, homeMean: hS / N, awayWin: (aW + tie / 2) / N, homeWin: 1 - (aW + tie / 2) / N,
              pOver: mt != null ? over / N : null, marketTotal: mt }
    };
  }

  // Correlation of two players' simulated fantasy points (for stacks / bring-backs).
  function correlation(res, idA, idB){
    var N = res.sims, a = res.index[idA] * N, b = res.index[idB] * N, ma = 0, mb = 0, s;
    for (s = 0; s < N; s++){ ma += res.fp[a + s]; mb += res.fp[b + s]; } ma /= N; mb /= N;
    var c = 0, va = 0, vb = 0;
    for (s = 0; s < N; s++){ var x = res.fp[a + s] - ma, y = res.fp[b + s] - mb; c += x * y; va += x * x; vb += y * y; }
    return va && vb ? c / Math.sqrt(va * vb) : 0;
  }

  root.SlateSim = { simulateGame: simulateGame, correlation: correlation, LG: LG };
})(typeof window !== 'undefined' ? window : globalThis);
