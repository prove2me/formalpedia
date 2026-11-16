-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_lb_offline_optimum
-- name    : RankCutFacility.Shifted.Supplement.lb_offline_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:30.096859+00:00
-- url     : https://prove2.me/theorems/e3fa72b6-5bc5-4d92-9d2b-c096c0b391bb
-- title:
--   Lemma 6.3 — $\mathrm{OPT}=1+N/3$ for every realization
-- statement:
--   On the instance of Section 6.1 ($N\ge2$, candidates $Y$, every opening cost one), let the $N$ demand points be any points $x_{w_1},\dots,x_{w_N}$ of $X$, repetitions allowed.
--
--   **Lemma 6.3.** For every realization of the $N$ demand points,
--
--   $$\mathrm{OPT}=1+\frac N3.$$
--
--   Because the offline cost does not depend on the realization, the expected lower bound of the i.i.d. experiment transfers to a single demand multiset.
--
--   Differences from the source:
--   - encoding: a realization of the N demand points (drawn from X) → an index map w : Fin N → Fin m; reason: the demand points of the experiment lie in X; repetitions are allowed
--   - encoding: OPT = min over O ⊆ F of opening plus connection cost → sInf over nonempty facility sets of the same cost; reason: the empty set has infinite cost in the source; the set of values is finite and nonempty, so sInf is the minimum
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma 6.3, printed p. 19 (PDF p. 21)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section

namespace RankCutFacility.Shifted.Supplement

/-- Lemma 6.3 (PDF p. 21, printed p. 19): for every realization `x_{w_1}, …, x_{w_N}` of the
demand points, `OPT = 1 + N/3` in the unit-cost prescribed-candidate instance. -/
theorem lb_offline_optimum (N : ℕ) (hN : 2 ≤ N) (w : Fin N → Fin (lbM N)) :
    offlineOpt (lbDist N) (lbSite N) (lbUnitFee N) (fun i => (Sum.inl (w i) : LBPoint N)) =
      1 + (N : ℝ) / 3 := by sorry

end RankCutFacility.Shifted.Supplement
