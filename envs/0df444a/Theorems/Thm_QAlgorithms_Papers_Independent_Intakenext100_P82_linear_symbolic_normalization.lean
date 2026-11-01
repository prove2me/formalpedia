-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_linear_symbolic_normalization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.linear_symbolic_normalization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:07:38.279002+00:00
-- url     : https://prove2.me/theorems/04f047b9-41d2-4d73-80d5-d02e843110a8
-- title:
--   Proposition 3: linear symbolic normalization cost
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   For the effective normalization problem there are one fixed symbolic program $A$ and a constant $K>0$, chosen before every input gate list $w$, that return $h,c,g$ with $c$ normalized, $g\in C$, and
--
--   $$[w]=H^h[c]g,\qquad \operatorname{cost}_A(w)\le K(|w|+1).$$
--
--   The execution consists only of constant-size finite table tests and stack operations; setup and the complete retained output are charged. This expresses the linear symbolic cost of Appendix C, including the empty input.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 3, Proposition 3: linear symbolic normalization cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Proposition 3, PDF p.3 and Appendix C, p.8.
Runtime includes actual execution, input scan and the retained output. -/
theorem linear_symbolic_normalization :
    ∃ p : Program, ∃ K : ℕ, 0 < K ∧ LinearNormalizes p K := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
