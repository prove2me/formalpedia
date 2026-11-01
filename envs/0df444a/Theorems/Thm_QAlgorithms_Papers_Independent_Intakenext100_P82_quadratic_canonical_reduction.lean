-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_quadratic_canonical_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.quadratic_canonical_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:08:17.605038+00:00
-- url     : https://prove2.me/theorems/8be89aef-f2e2-4c8a-8ce9-7e574f63d7f3
-- title:
--   Proposition 4: quadratic worst-case canonical reduction cost
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   There are a fixed symbolic reduction procedure $B$ and a universal constant $K>0$ such that every already computed normalized presentation $o=H^h[c]g$ is converted to actual Clifford gates $g_1,g_2$ and a canonical word $d$ satisfying
--
--   $$[o]=g_1[d]g_2,\qquad \operatorname{cost}_B(o)\le K(\tau(c)+1)^2.$$
--
--   The bound is a worst-case upper bound on the phase after normalization, including its input and output lists. Raw-input normalization is separately linear in the raw gate-list length.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 3, Proposition 4: quadratic worst-case canonical reduction cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Proposition 4, PDF p.3 and Appendix D, pp.8--9.
This is the quadratic upper bound for the phase after normalization. -/
theorem quadratic_canonical_reduction :
    ∃ p : Program, ∃ K : ℕ, 0 < K ∧ QuadraticReduces p K := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
