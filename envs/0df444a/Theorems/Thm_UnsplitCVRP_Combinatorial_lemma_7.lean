-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_7
-- name    : UnsplitCVRP.Combinatorial.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:00.464098+00:00
-- url     : https://prove2.me/theorems/90bab6e4-4adf-4883-a05b-4dc391de391a
-- title:
--   Lemma 7, p. 5 — the δ-tank tour-splitting bound
-- statement:
--   Let $A$ be a depot TSP tour of distinct clients in visiting order, with metric travel cost $c(A)$. For $\delta\in[0,1/2]$, classify the clients of $A$ as small or big according to their demands. The minimum cost $\operatorname{Split}(A)$ of a capacity-feasible partition of that order into consecutive tours satisfies
--   $$
--   \operatorname{Split}(A)\le c(A)
--     +\frac{\mathcal D_{\rm small}}{1-\delta}
--     +\frac{2\mathcal D_{\rm big}}{1-\delta}
--     -\frac{\delta\mathcal D'_{\rm big}}{1-\delta}.
--   $$
--   This is the tank guarantee used by both branches of Algorithm 1.
--
--   **Formalization Note** The statement applies to any client subset because Algorithm 1 uses it both for small clients and for all clients. The printed phrase “with cost” is read as an upper bound. The $O(n^2)$ running time is outside this cost formalization.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 5, Lemma 7 and display (1); deterministic optimal split on p. 7

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Lemma 7, p. 5: the δ-tank guarantee for an ordered client set. -/
theorem lemma_7 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (A : List (Fin (n + 1))) (hAn : A.Nodup)
    (hA0 : (0 : Fin (n + 1)) ∉ A) :
    bestSplit c d A ≤ SupplyChainTheory.routeCost c A +
      1 / (1 - δ) * radial c d (smallIn d δ A.toFinset) +
      2 / (1 - δ) * radial c d (bigIn d δ A.toFinset) -
      δ / (1 - δ) * radialCount c (bigIn d δ A.toFinset) := by sorry

end UnsplitCVRP.Combinatorial
