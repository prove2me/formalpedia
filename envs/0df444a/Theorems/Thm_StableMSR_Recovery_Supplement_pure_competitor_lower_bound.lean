-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_pure_competitor_lower_bound
-- name    : StableMSR.Recovery.Supplement.pure_competitor_lower_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-19T16:12:51.846195+00:00
-- url     : https://prove2.me/theorems/4331d277-19ad-4780-9c25-d32818f790c5
-- title:
--   Runner-up lower bound for competitors that separate the dummy points from the source and hub
-- statement:
--   Consider the metric construction of Lemma C.1 with a nonempty source, one hub, and $k+1$ dummies, where $1\le k\le n$. Assume the source diameter is smaller than the hub radius $R_0$, and $R_0<\delta$, the distance between distinct dummies. Let $Q$ be a feasible exact-$(k+2)$ partition different from the supplied partition. Suppose each block lies wholly on the source-plus-hub side or wholly on the dummy side. Then
--   $$
--   \operatorname{cost}(Q)\ge\delta+\operatorname{OPT}_k(Y).
--   $$
--   The counting argument forces a nonsingleton dummy block. When the hub is isolated, the source occupies at most $k$ blocks. When the hub shares a block with a source point, that block already contributes $R_0$.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix C, Lemma C.1, p. 24, unmixed-partition case.

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem pure_competitor_lower_bound {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d)
    (hD : diameter d Finset.univ < hubRadius d γ τ)
    (hδ : hubRadius d γ τ < dummyDistance d γ τ)
    (Q : Partition (n+k+2)) (hQ : Feasible Finset.univ (k+2) Q)
    (hne : Q ≠ suppliedPartition n k)
    (hpure : ∀ C ∈ Q, C ⊆ hubSource n k ∨ ∀ x ∈ C, n < x.val) :
    dummyDistance d γ τ + optimumValue d k ≤ cost (hubDistance d k γ τ) Q := by sorry

end StableMSR.Recovery.Supplement
