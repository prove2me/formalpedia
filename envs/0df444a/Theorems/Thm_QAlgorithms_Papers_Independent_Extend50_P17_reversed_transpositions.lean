-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_reversed_transpositions
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.reversed_transpositions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:58:08.917087+00:00
-- url     : https://prove2.me/theorems/76194a7a-62dc-4f5c-b8ad-902254047ac4
-- title:
--   Lemma 6 / Eq.(37): reversed-transposition identity
-- statement:
--   Let $k\ge1$, $k\le N$, and let $a_1,\ldots,a_k$ and $b_1,\ldots,b_k$ each be distinct port indices in $\{1,\ldots,N\}$; overlaps between the lists are allowed. Define $P_0=1$, $L_s=(a_s,P_{s-1}(b_s))$, and $P_s=L_sP_{s-1}$. Define $L'_s$ by the same recursion with $a,b$ interchanged. Products act rightmost first and swapping equal indices is the identity. For $1\le s\le k$,
--
--   $$L'_sL'_{s-1}\cdots L'_1=L_1L_2\cdots L_s.$$
--
--   Equivalently, the two accumulated permutations are inverses. The recursive construction, rather than arbitrary permutations, is essential.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Lemma 6 / Eq.(37): reversed-transposition identity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Lemma 6, Eq.(37): reversed recursive transposition identity. -/
theorem reversed_transpositions (N k : ℕ) (hk : 1 ≤ k) (hNk : k ≤ N)
    (a b : MPBTPortSelection N k) (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ k) :
    accumulated b a s = (accumulated a b s)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
