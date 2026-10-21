-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_6
-- name    : UnsplitCVRP.Combinatorial.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:56.96158+00:00
-- url     : https://prove2.me/theorems/146417fb-f397-42ba-a7d8-00fdc65211ef
-- title:
--   Lemma 6, p. 4 — the radial lower bound
-- statement:
--   Let $V$ be the clients of a normalized unsplittable CVRP instance, with metric cost $c$, demands $d_v\in(0,1]$, and capacity $1$. For every feasible solution $\mathcal T$,
--   $$
--   \mathcal D:=\sum_{v\in V}2d_vc(r,v)\le c(\mathcal T).
--   $$
--   Thus the radial sum lower-bounds the optimum cost.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 4, Lemma 6

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Lemma 6, p. 4: the radial sum lower-bounds every feasible solution cost. -/
theorem lemma_6 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (R : List (List (Fin (n + 1))))
    (hR : IsSolution d R) :
    radial c d (clients n) ≤ SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial
