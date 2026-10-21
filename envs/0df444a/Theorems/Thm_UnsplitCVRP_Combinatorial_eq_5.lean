-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_eq_5
-- name    : UnsplitCVRP.Combinatorial.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:07.65303+00:00
-- url     : https://prove2.me/theorems/8fa81dec-c23d-475b-b334-fb1d5142e5a1
-- title:
--   Display (5), p. 8 — corrected upper bound for second branch cost
-- statement:
--   Let $A_a$ be an $\alpha$-approximate TSP tour through all clients and let $\mathcal T$ be any feasible CVRP solution. The all-client consecutive split in Algorithm 1 obeys
--   $$
--   \operatorname{Split}(A_a)\le
--     \alpha c(\mathcal T)+\tfrac32\mathcal D_{\rm small}
--     +3\mathcal D_{\rm big}-\tfrac12\mathcal D'_{\rm big}.
--   $$
--   This is the second branch estimate used in the final average.
--
--   **Formalization Note** Display (5) prints an equality, but the substituted TSP and tank estimates are upper bounds. The faithful usable statement is the displayed inequality.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 8, corrected reading of display (5)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Corrected display (5), p. 8: its printed equality is an upper bound. -/
theorem eq_5 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (α : ℝ) (hα : 1 ≤ α)
    (Aa : List (Fin (n + 1)))
    (hAa : IsTourOn (clients n) Aa)
    (hcAa : SupplyChainTheory.routeCost c Aa ≤ α * tspOn c (clients n))
    (R : List (List (Fin (n + 1)))) (hR : IsSolution d R) :
    bestSplit c d Aa ≤
      α * SupplyChainTheory.solutionCost c R +
      3 / 2 * radial c d (smallIn d (1 / 3 : ℝ) (clients n)) +
      3 * radial c d (bigIn d (1 / 3 : ℝ) (clients n)) -
      1 / 2 * radialCount c (bigIn d (1 / 3 : ℝ) (clients n)) := by sorry

end UnsplitCVRP.Combinatorial
