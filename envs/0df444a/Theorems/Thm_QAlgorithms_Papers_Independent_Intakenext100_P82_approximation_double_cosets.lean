-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_approximation_double_cosets
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.approximation_double_cosets
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:09:21.023111+00:00
-- url     : https://prove2.me/theorems/5cd86866-e932-4083-a64d-7d57a9e8fa9e
-- title:
--   Corollary 1: reduction of optimal approximation to Clifford double cosets
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   Let $U$ be any single-qubit projective gate, $\epsilon>0$, and $t\in\mathbb N$. Put $d(U,V)=\sqrt{2-|\operatorname{tr}(UV^\dagger)|}/2$. Then
--
--   $$\exists w:\ \operatorname{cost}_T(w)<t,\ d([w],U)<\epsilon
--   \quad\Longleftrightarrow\quad
--   \exists c\text{ canonical},\ g_1,g_2\in C:\ \tau(c)<t,\ d([c],g_1Ug_2)<\epsilon.$$
--
--   The left-hand word is a Clifford/T presentation, so it expresses the minimum charged non-Clifford cost convention of §IV. This reduces bounded-cost approximation to the Clifford double coset; both inequalities are strict.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 3, Corollary 1: reduction of optimal approximation to Clifford double cosets

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Corollary 1, PDF p.3, §IV metric and charged cost pp.3--4.
Both distance and integer cost cutoffs are strict. -/
theorem approximation_double_cosets (U : Mat) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (t : ℕ) :
    (∃ w : List CTLetter, chargedT w < t ∧ gateDistance (ctValue w) U < epsilon) ↔
    (∃ c : List Syllable, BsCanonical c ∧ bsTCount c < t ∧
      ∃ g1 g2 : Fin 24,
        gateDistance (syllableValue c) (cliffordMatrix g1 * U * cliffordMatrix g2) < epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
