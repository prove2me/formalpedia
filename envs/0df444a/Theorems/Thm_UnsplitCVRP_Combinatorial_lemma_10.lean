-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_10
-- name    : UnsplitCVRP.Combinatorial.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:04.823362+00:00
-- url     : https://prove2.me/theorems/a7493a2d-98fd-4165-ac5e-6ad6e9c759b1
-- title:
--   Lemma 10, p. 8 — the auxiliary matching costs at most opt
-- statement:
--   At threshold $\delta=1/3$, every feasible CVRP route contains at most two big clients. Let $\operatorname{cost}(M)$ be the minimum cost of a loop-allowed perfect matching of the auxiliary graph on the big clients, with each edge represented by its one- or two-client depot route. For every feasible solution $\mathcal T$,
--   $$
--   \operatorname{cost}(M)\le c(\mathcal T).
--   $$
--   This bounds the matching branch of Algorithm 1 against the CVRP optimum.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 8, Lemma 10 (auxiliary graph p. 7)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Lemma 10, p. 8: the auxiliary matching cost is at most the optimum. -/
theorem lemma_10 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (R : List (List (Fin (n + 1))))
    (hR : IsSolution d R) :
    matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) ≤
      SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial
