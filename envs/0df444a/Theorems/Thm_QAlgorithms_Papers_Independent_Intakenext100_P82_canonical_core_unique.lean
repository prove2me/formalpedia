-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_canonical_core_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.canonical_core_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:05:30.572019+00:00
-- url     : https://prove2.me/theorems/e1a0c592-a91d-4e44-8cba-a039ae495108
-- title:
--   Theorem 1: uniqueness of the canonical core under two-sided Clifford equivalence (seed result)
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   Let $c_1,c_2$ be canonical syllable words. If there are $g_1,g_2\in C$ with $[c_2]=g_1[c_1]g_2$ as projective gates, then
--
--   $$c_1=c_2$$
--
--   as words in the two-letter alphabet. This gives a unique canonical core for each Clifford double coset. It makes no uniqueness assertion about the surrounding Clifford gates.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 3, Theorem 1: uniqueness of the canonical core under two-sided Clifford equivalence (seed result)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Theorem 1, PDF p.3, grammar p.2, proof pp.9--10.
Only the canonical syllable cores are syntactically equal. -/
theorem canonical_core_unique (c1 c2 : List Syllable)
    (h1 : BsCanonical c1) (h2 : BsCanonical c2)
    (heq : ∃ g1 g2 : Fin 24,
      SameGate (syllableValue c2) (cliffordMatrix g1 * syllableValue c1 * cliffordMatrix g2)) :
    c1 = c2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
