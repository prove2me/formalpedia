-- Prove2me | Theorems.Thm_PrivOptTest_lemma_3_8
-- name    : PrivOptTest.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:50.989163+00:00
-- url     : https://prove2.me/theorems/ccf2c25b-65d2-4a1f-bfb6-99025c072e50
-- title:
--   Lemma 3.8, p.17 — at most one common trie node per depth
-- statement:
--   Let $A,B$ be lists of $b$-bit records that satisfy the promise (all of $A$ below all of $B$, or all above). Then for every depth $0\le\ell\le b$
--   $$\big|\{p\in\{0,1\}^\ell:\ |B^\ell_p|\cdot|A^\ell_p|\ne0\}\big|\le1,$$
--   and at depth $b$ no node is common.
--
--   This uniqueness of the common node is what the final statistics of Algorithm 2 exploit.
--
--   Differences from the source:
--   - generalization: two sequences of length n → lists of any lengths; reason: the lengths are not used
--   - generalization: depths ℓ ∈ [b] → depths 0 ≤ ℓ ≤ b; reason: depth 0 has a single node; specializes to the source
--   - encoding: "the promise holds" → Promise A B: all Alice records below all Bob records, or all above; reason: the proof opens with exactly this disjunction
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.8 and Definition 3.7, p.17

import Mathlib
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Lemma 3.8** (p.17). Under the promise, at every depth `ℓ` at most one node of the binary trie is
common, `|{p ∈ {0,1}^ℓ : |B^ℓ_p| · |A^ℓ_p| ≠ 0}| ≤ 1`, and at depth `b` none is.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 3.8 and Definition 3.7, p.17.

**Formalization Note.** Records are `b`-bit strings read as integers below `2^b`; node `p` at depth `ℓ`
is an integer below `2^ℓ` and holds the records with `prefix_ℓ(x) = ⌊x / 2^{b−ℓ}⌋ = p`. The promise is
`Promise A B`: every Alice record is below every Bob record, or every one is above (the two strict
orders of Lemma 3.5 after the lifting of Remark 3.6). The datasets are lists of any lengths. Depth `0`
is included (one node). -/
theorem lemma_3_8 (b : ℕ) (A B : List ℕ) (hA : ∀ x ∈ A, x < 2 ^ b) (hB : ∀ x ∈ B, x < 2 ^ b)
    (h : Promise A B) :
    (∀ ℓ ≤ b, ((Finset.range (2 ^ ℓ)).filter fun p =>
        nodeCount b ℓ B p * nodeCount b ℓ A p ≠ 0).card ≤ 1) ∧
      ((Finset.range (2 ^ b)).filter fun p =>
        nodeCount b b B p * nodeCount b b A p ≠ 0).card = 0 := by sorry

end PrivOptTest
