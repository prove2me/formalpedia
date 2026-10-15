-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_C_2_delta
-- name    : OutpatientWalkIn.SmallCap.proposition_C_2_delta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:39.355597+00:00
-- url     : https://prove2.me/theorems/d3cff2cc-7eea-4a8c-bdd8-3b0a917f2769
-- title:
--   Proposition C.2 (δ-part), Online App. p. 8 — π(δ, μ_S) is continuous and strictly decreasing in δ ≥ 0
-- statement:
--   Let $\lambda > 0$ and $\mu_S > 0$ be fixed, and let $\pi(\delta,\mu_S)$ be the blocking probability of the M/D/1/K−1+p queue with $K=\lceil\delta\mu_S\rceil$ and $p=\delta\mu_S+1-K$ (Corollary C.1). Then the map
--   $$\delta \;\longmapsto\; \pi(\delta,\mu_S)$$
--   is continuous and strictly decreasing on $[0,\infty)$.
--
--   A longer delay threshold means a larger buffer and fewer blocked patients. Continuity across the points where $\delta\mu_S$ is an integer, where $K$ jumps and $p$ resets, is what makes the observable equilibrium threshold well defined.
--
--   **Formalization Note** Proposition C.2 asserts monotonicity and continuity in $\delta$ and in $\mu_S$ separately. This item is the $\delta$ half. The $\mu_S$ half is a milestone of the companion mission on the triage model.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 8, Proposition C.2 (monotonicity and continuity in δ)

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.SmallCap
theorem proposition_C_2_delta (lam : ℝ) (hlam : 0 < lam) (μS : ℝ) (hμS : 0 < μS) :
    StrictAntiOn (fun δ => blockProb lam δ μS) (Set.Ici 0) ∧ ContinuousOn (fun δ => blockProb lam δ μS) (Set.Ici 0) := by sorry
end OutpatientWalkIn.SmallCap
