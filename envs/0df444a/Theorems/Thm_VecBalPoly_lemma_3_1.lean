-- Prove2me | Theorems.Thm_VecBalPoly_lemma_3_1
-- name    : VecBalPoly.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:18:44.559118+00:00
-- url     : https://prove2.me/theorems/628d85a3-c40c-497d-975f-295dd641ae97
-- title:
--   Lemma 3.1 — tracking error of entry removal
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have columns of Euclidean norm at most $1$, with $n>K$. In every run of Algorithm 2.2, the sum of the absolute values of the entries removed from any row by the dominant-entry rule is at most $2K$:
--   $$\sum_{j\in D_i}|a_{ij}|\le 2K.$$
--   At every state before the final rounding (after each cleanup, and after each update before its cleanup),
--   $$|(Ax)_i-d_i|\le4K\qquad\text{for every row } i.$$
--
--   This turns the tracked row sums, which the algorithm controls, into the true row sums of the coloring.
--
--   Differences from the source:
--   - generalization: the states of Algorithm 2.2, whose step 1 computes h by the procedure of Lemma 2.1 → every prefix run whose directions are any vectors meeting Lemma 2.1's conclusion (GoodDir); reason: the paper's procedure returns such vectors (Lemma 2.1), so its runs are among these; the proof uses only those guarantees
--   - reading: no hypothesis on A printed in this statement → columns of Euclidean norm at most 1 and n > K; reason: the standing hypothesis of Theorem 1.1, under which Algorithm 2.2 runs; for n ≤ K the algorithm makes no update
--   - reading: "at every state before the final rounding" → the states after each cleanup and the states right after each update, before its cleanup; reason: these are the states between the algorithm's steps; inside a cleanup x is fixed and d_i is preserved
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: the entries removed from row i by the dominant-entry rule (D_i in the proof, p.7) → the ghost state field Dom i, written by the removal step of cleanup and read by nothing else; reason: the algorithm never reads it; the sum runs over exactly the removed entries
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_VecBalPoly_IsPrefixRun

namespace VecBalPoly

open Matrix

/-- **Lemma 3.1 (tracking error of entry removal).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 3.1, p.7 (PDF p.8): "The sum of the absolute values of entries removed by the
dominant-entry rule from any row is at most 2K. At every state before the final rounding, we have
|(Ax)i − di| ≤ 4K for every row i."

**Formalization Note** The entries removed from row `i` by the dominant-entry rule are the
ghost set `Domᵢ` of the state. "Every state before the final rounding" covers the states after
each cleanup (`sts k`, `k ≤ N`) and the states right after each update, before its cleanup
(`preState`). -/
theorem lemma_3_1 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), (∀ j, ∑ i, A i j ^ 2 ≤ 1) → K < (n : ℝ) →
      ∀ (N : ℕ) (sts : ℕ → St m n) (hs : ℕ → Fin n → ℝ), IsPrefixRun A N sts hs →
        (∀ k ≤ N, ∀ i, ∑ j ∈ (sts k).Dom i, |A i j| ≤ 2 * K ∧
          |(A *ᵥ (sts k).x) i - d A (sts k) i| ≤ 4 * K) ∧
        (∀ k < N, ∀ i,
          |(A *ᵥ (preState (sts k) (hs k)).x) i - d A (preState (sts k) (hs k)) i| ≤ 4 * K) := by sorry

end VecBalPoly
