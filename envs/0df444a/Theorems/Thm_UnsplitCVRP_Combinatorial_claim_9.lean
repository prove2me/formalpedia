-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_claim_9
-- name    : UnsplitCVRP.Combinatorial.claim_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:07.507329+00:00
-- url     : https://prove2.me/theorems/6a008519-f220-42ba-a177-128a4353da1e
-- title:
--   Claim 9, p. 6 — probability of four depot-edge copies
-- statement:
--   Under the random tiling of Lemma 7, let $v_i$ be a big client, so $d_{v_i}>\delta$ with $\delta\in[0,1/2]$. The construction adds four copies of the edge $(r,v_i)$ when a tile endpoint lies within the first $d_{v_i}-\delta$ units of that client's cumulative-demand interval. Then
--   $$
--   \Pr[4\text{ copies of }(r,v_i)\text{ added}]
--     =\frac{d_{v_i}-\delta}{1-\delta}.
--   $$
--   This gives the correction term for big clients in the tank bound.
--
--   **Formalization Note** The event uses the closed right endpoint in Claim 9's proof. The construction paragraph on p. 5 prints a strict right endpoint; the difference has Lebesgue measure zero.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 6, Claim 9 and its proof

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Claim 9, p. 6: probability of four depot-edge copies for a big client. -/
theorem claim_9 {n : ℕ} (d : Fin (n + 1) → ℝ) (hd : Demands d)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (A : List (Fin (n + 1))) (hAn : A.Nodup)
    (hA : (0 : Fin (n + 1)) ∉ A)
    (i : ℕ) (hi : i < A.length) (hbig : δ < d (A.getD i 0)) :
    (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc 0 (1 - δ) ∧
      IsFourCopies d δ A i θ}).toReal / (1 - δ) =
      (d (A.getD i 0) - δ) / (1 - δ) := by sorry

end UnsplitCVRP.Combinatorial
