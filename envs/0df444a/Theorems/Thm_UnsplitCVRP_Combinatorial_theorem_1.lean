-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_theorem_1
-- name    : UnsplitCVRP.Combinatorial.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:08.344059+00:00
-- url     : https://prove2.me/theorems/452e37e2-6897-41dc-a40c-8683c5c322bc
-- title:
--   Theorem 1, p. 2 — Algorithm 1 is an (α + 1.75)-approximation
-- statement:
--   Consider a normalized unsplittable CVRP instance with metric costs and positive client demands at most $1$. Let $A_s$ and $A_a$ visit exactly the small clients and all clients, respectively, each at cost at most $\alpha$ times the corresponding minimum TSP tour cost, where $\alpha\ge1$. Define $C_{\rm alg}$ as the cheaper of the auxiliary big-client matching plus the minimum consecutive split of $A_s$, and the minimum consecutive split of $A_a$, both at $\delta=1/3$. Then $C_{\rm alg}$ is attained by a feasible solution, and for every feasible solution $\mathcal T$,
--   $$
--   C_{\rm alg}\le(\alpha+1.75)c(\mathcal T).
--   $$
--   Thus the particular two-branch algorithm of §3 achieves the claimed approximation ratio.
--
--   **Formalization Note** The requirement $\alpha\ge1$ makes explicit the lower bound implicit in “approximation ratio.” The tour and matching outputs are represented by their attained optimal costs; polynomial running time is not asserted.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 2, Theorem 1; proof §3, pp. 7–9

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Theorem 1, p. 2: Algorithm 1 returns an (α + 1.75)-approximation. -/
theorem theorem_1 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (α : ℝ) (hα : 1 ≤ α)
    (As Aa : List (Fin (n + 1)))
    (hAs : IsTourOn (smallIn d (1 / 3 : ℝ) (clients n)) As)
    (hAa : IsTourOn (clients n) Aa)
    (hcAs : SupplyChainTheory.routeCost c As ≤
      α * tspOn c (smallIn d (1 / 3 : ℝ) (clients n)))
    (hcAa : SupplyChainTheory.routeCost c Aa ≤ α * tspOn c (clients n)) :
    (∃ R, IsSolution d R ∧
      SupplyChainTheory.solutionCost c R = alg1Cost c d As Aa) ∧
    ∀ R, IsSolution d R →
      alg1Cost c d As Aa ≤ (α + 7 / 4) * SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial
