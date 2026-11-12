-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_lemma_3_1
-- name    : ReadOnceParityBP.LowerBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:12.061193+00:00
-- url     : https://prove2.me/theorems/6fd855a1-b038-46a2-b2c5-830953d4b815
-- title:
--   Lemma 3.1 — leader cut and noncrossing forward edges
-- statement:
--   Let n be even, let B⊆{0,…,n−1} have size n/2, and construct σ_B by canonical deletion. Compute its leader ℓ as the smallest j∈B with σ_B(j)<j, or zero if no such j exists. Cut the cycle into the order ℓ,…,n−1,0,…,ℓ−1. For each j∈B write a_j and b_j for the positions of j and σ_B(j) in this order. Then
--
--   $$\text{no distinct }j,k\in B\text{ have }\min(a_j,b_j)<\min(a_k,b_k)<\max(a_j,b_j)<\max(a_k,b_k),$$
--   $$0<\operatorname{cwDist}(j,v)<\operatorname{cwDist}(j,\sigma_B(j))\iff a_j<\operatorname{pos}(v)<b_j,$$
--   $$a_j<b_j\quad(j\in B).$$
--
--   The first clause states noncrossing, the second that clockwise interiors do not wrap across the cut, and the third left-to-right orientation. The leader and matching are computed; none of these conclusions is assumed.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - generalization: positive even cycle lengths → also the empty cycle n=0; reason: the unique half-subset is empty; its empty matching makes the geometric clauses vacuous and its polynomial and exact count equal one
--   - encoding: noncrossing, not wrapping, and all arrows left to right → interleaving-endpoint exclusion, clockwise-interior equivalence, and strict cut-position order; reason: these make all three geometric clauses explicit; universal ordered pairs exclude both crossing orientations
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Lemma 3.1 p.7, proof pp.7–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Lemma 3.1 (p. 7): cut the cycle `ℤ_n` at the leader `ℓ` of `σ_B`, giving the interval
`ℓ, ℓ+1, …, n-1, 0, 1, …, ℓ-1` (positions `cutPos n ℓ`), and draw a directed edge from `j` to
`σ_B(j)` for each `j ∈ B`. Then
1. the edges are non-crossing: no two edges `{a, b}`, `{c, d}` (as position intervals) satisfy
   `a < c < b < d`;
2. no edge wraps around: the elements strictly inside the clockwise arc from `j` to `σ_B(j)`
   are exactly the elements strictly between them in the interval;
3. every edge goes from left to right. -/
theorem lemma_3_1 (n : ℕ) (hn : Even n) (B : Finset (Fin n)) (hB : B.card = n / 2) :
    (∀ j ∈ B, ∀ k ∈ B, j ≠ k →
      ¬ (min (cutPos n (leader B) j) (cutPos n (leader B) (sigma B j)) <
            min (cutPos n (leader B) k) (cutPos n (leader B) (sigma B k)) ∧
          min (cutPos n (leader B) k) (cutPos n (leader B) (sigma B k)) <
            max (cutPos n (leader B) j) (cutPos n (leader B) (sigma B j)) ∧
          max (cutPos n (leader B) j) (cutPos n (leader B) (sigma B j)) <
            max (cutPos n (leader B) k) (cutPos n (leader B) (sigma B k)))) ∧
    (∀ j ∈ B, ∀ v : Fin n,
      (0 < cwDist j v ∧ cwDist j v < cwDist j (sigma B j)) ↔
        (cutPos n (leader B) j < cutPos n (leader B) v ∧
          cutPos n (leader B) v < cutPos n (leader B) (sigma B j))) ∧
    (∀ j ∈ B, cutPos n (leader B) j < cutPos n (leader B) (sigma B j)) := by sorry

end ReadOnceParityBP.LowerBound
