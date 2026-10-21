-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_eq_4
-- name    : UnsplitCVRP.Combinatorial.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:16.342456+00:00
-- url     : https://prove2.me/theorems/f3dd636d-9dcf-4376-a64a-2b43810b6e59
-- title:
--   Display (4), p. 8 — first branch cost
-- statement:
--   Let $A_s$ be an $\alpha$-approximate TSP tour through exactly the small clients, and let $\mathcal T$ be any feasible CVRP solution. Algorithm 1's first branch has cost $\operatorname{cost}(M)+\operatorname{Split}(A_s)$, and display (4) bounds it by
--   $$
--   \operatorname{cost}(M)+\operatorname{Split}(A_s)
--     \le \operatorname{cost}(M)+\alpha c(\mathcal T)
--       +\tfrac32\mathcal D_{\rm small}.
--   $$
--   This isolates the matching-plus-tank branch before the final comparison.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 8, display (4)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Display (4), p. 8: bound for the matching-plus-small-tour solution. -/
theorem eq_4 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (α : ℝ) (hα : 1 ≤ α)
    (As : List (Fin (n + 1)))
    (hAs : IsTourOn (smallIn d (1 / 3 : ℝ) (clients n)) As)
    (hcAs : SupplyChainTheory.routeCost c As ≤
      α * tspOn c (smallIn d (1 / 3 : ℝ) (clients n)))
    (R : List (List (Fin (n + 1)))) (hR : IsSolution d R) :
    matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) + bestSplit c d As ≤
      matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) +
        α * SupplyChainTheory.solutionCost c R +
        3 / 2 * radial c d (smallIn d (1 / 3 : ℝ) (clients n)) := by sorry

end UnsplitCVRP.Combinatorial
