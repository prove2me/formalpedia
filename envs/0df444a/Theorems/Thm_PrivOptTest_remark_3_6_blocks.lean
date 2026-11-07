-- Prove2me | Theorems.Thm_PrivOptTest_remark_3_6_blocks
-- name    : PrivOptTest.remark_3_6_blocks
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:50.525557+00:00
-- url     : https://prove2.me/theorems/6e32e43f-b3a0-488b-b3f4-15d0c3578431
-- title:
--   Remark 3.6, p.16 — the blocks of neighbouring datasets are neighbouring
-- statement:
--   Let $S,S'$ be datasets of size $n$ that differ in exactly one record. Then for every $k$ the blocks $S^{\uparrow}_k$ and $S'^{\uparrow}_k$ of the $k$ largest records differ, as multisets, by at most one replacement, and so do the blocks $S^{\downarrow}_k$, $S'^{\downarrow}_k$ of the $k$ smallest.
--
--   This is what lets the algorithm run on the blocks alone while keeping differential privacy with respect to the full datasets.
--
--   Differences from the source:
--   - generalization: k ∈ [n], records in {0,1}^b → every k and natural-number records; reason: specializes to the source; for k ≥ n the blocks are the whole datasets
--   - encoding: "these subsets also respect the neighboring condition" → as multisets the blocks differ by one replacement (OneReplaced); reason: neighbouring means one record replaced (§2.1, p.13); as sorted sequences the blocks may differ in every position
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Remark 3.6, p.16

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Remark 3.6** (p.16), block neighbouring: if two datasets are neighbours (one record replaced),
then their blocks `S↑_k` of the `k` largest records, and their blocks `S↓_k` of the `k` smallest, also
differ by at most one replacement, as multisets.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Remark 3.6, p.16.

**Formalization Note.** Blocks are sorted lists (`blockUp`, `blockDown`). As sorted sequences they can
differ in every position, so the claim is about multisets (`OneReplaced`). It holds for every `k`;
for `k ≥ n` the blocks are the whole datasets. -/
theorem remark_3_6_blocks {n : ℕ} (S S' : Fin n → ℕ) (k : ℕ)
    (h : PrivLearn.Generic.Neighbors S S') :
    OneReplaced (blockUp k S) (blockUp k S') ∧ OneReplaced (blockDown k S) (blockDown k S') := by sorry

end PrivOptTest
