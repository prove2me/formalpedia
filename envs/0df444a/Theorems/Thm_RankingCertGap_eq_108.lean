-- Prove2me | Theorems.Thm_RankingCertGap_eq_108
-- name    : RankingCertGap.eq_108
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:32.027688+00:00
-- url     : https://prove2.me/theorems/92ba0575-ea44-46de-b9a5-8fc7a1e5892a
-- title:
--   Display (108), p.35 — local probability inequality on two-regular instances
-- statement:
--   Let $G$ be a nonempty two-regular instance and $(i^\star,j^\star)\in E(G)$. Then
--
--   $$
--   \Pr[X_{j^\star}=1]\ge3\Pr[X_{i^\star}=0].
--   $$
--
--   This is the inequality behind the constant gain split: it gives $\Phi_G(i^\star,j^\star;\tilde f^\star_2)\ge3/4$ on every edge.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), eq. (108), p.35; App. I.2, pp.76–77

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun
import Definitions.Def_RankingCertGap_Score

open MeasureTheory

namespace RankingCertGap

/-- **Display (108).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), p.35 and App. I.2, pp.76–77:
for `G ∈ B₂` and `(i★, j★) ∈ E(G)`, `Pr[X_{j★} = 1] ≥ 3 Pr[X_{i★} = 0]`. -/
theorem eq_108 {m n : ℕ} (G : Inst m n) (hG : G.IsRegular 2) (i : Fin m) (j : Fin n)
    (hij : G.Edge i j) :
    3 * (rankMeasure m).real {Y | ¬ taken (G.run Y n) i} ≤
      (rankMeasure m).real {Y | (G.run Y n j).isSome = true} := by sorry

end RankingCertGap
