-- Prove2me | Theorems.Thm_PrivOptTest_lemma_3_10
-- name    : PrivOptTest.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:53.725531+00:00
-- url     : https://prove2.me/theorems/a9045d55-ec67-4356-88a5-29a59fdf0e4c
-- title:
--   Lemma 3.10, p.17 — the escaped-points function is non-decreasing from 0 to n
-- statement:
--   Let $A,B$ be lists of $n$ records in $\{0,1\}^b$ satisfying the promise, and $F(\ell)=n-\max_{p\in\{0,1\}^\ell}\min\{|A^\ell_p|,|B^\ell_p|\}$. Then $F$ is non-decreasing on $\{0,\dots,b\}$, $F(0)=0$ and $F(b)=n$.
--
--   $F$ is the quantity located by the private binary search of Algorithm 2.
--
--   Differences from the source:
--   - reading: F : [b] → ℕ → F on {0, …, b}; reason: the lemma asserts F(0) = 0, so depth 0 is in the domain
--   - encoding: min{A^ℓ_p, B^ℓ_p} → minimum of the node cardinalities; reason: as in the proof; sequences are lists of length n
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.10, p.17

import Mathlib
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Lemma 3.10** (escaped points, p.17). Under the promise, for two datasets of size `n` the
function `F(ℓ) = n − max_{p∈{0,1}^ℓ} min{|A^ℓ_p|, |B^ℓ_p|}` is non-decreasing on `0, …, b`, with
`F(0) = 0` and `F(b) = n`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.10, p.17.

**Formalization Note.** `F` is `escaped n b ℓ A B`; the minimum is over node cardinalities, as in the
proof. Records are integers below `2^b`; the promise is `Promise A B` (Lemma 3.8). The paper's domain
`[b]` is read as `0, …, b`, since the lemma asserts `F(0) = 0`. -/
theorem lemma_3_10 (b n : ℕ) (A B : List ℕ) (hAl : A.length = n) (hBl : B.length = n)
    (hA : ∀ x ∈ A, x < 2 ^ b) (hB : ∀ x ∈ B, x < 2 ^ b) (h : Promise A B) :
    (∀ ℓ, ℓ + 1 ≤ b → escaped n b ℓ A B ≤ escaped n b (ℓ + 1) A B) ∧
      escaped n b 0 A B = 0 ∧ escaped n b b A B = n := by sorry

end PrivOptTest
