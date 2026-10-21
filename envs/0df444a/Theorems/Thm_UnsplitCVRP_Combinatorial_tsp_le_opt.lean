-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_tsp_le_opt
-- name    : UnsplitCVRP.Combinatorial.tsp_le_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:10.56313+00:00
-- url     : https://prove2.me/theorems/22124078-6877-42fa-947e-034a1caa0e56
-- title:
--   §3.1, p. 8 — an optimal TSP tour on a client subset costs at most opt
-- statement:
--   Let $S\subseteq V$ be any set of clients in a normalized unsplittable CVRP instance. Write $\operatorname{TSP}(S)$ for the minimum length of a depot tour through exactly $S$. Every feasible CVRP solution $\mathcal T$ satisfies
--   $$
--   \operatorname{TSP}(S)\le c(\mathcal T).
--   $$
--   This applies to both TSP tours used by Algorithm 1: the small clients and all clients.
--
--   **Formalization Note** The paper states the lower bound for the tours used in §3.1. The subset form makes both applications explicit; the metric supplies shortcutting.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 8, §3.1 paragraph preceding display (4)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- The TSP lower bound used in §3.1, p. 8, also for a subset of clients. -/
theorem tsp_le_opt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (S : Finset (Fin (n + 1)))
    (hS : S ⊆ clients n) (R : List (List (Fin (n + 1))))
    (hR : IsSolution d R) :
    tspOn c S ≤ SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial
