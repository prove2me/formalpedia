-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_syllable_identities_and_basis
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.syllable_identities_and_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:10:35.626606+00:00
-- url     : https://prove2.me/theorems/a9cae0c5-eda7-4059-a1ae-9f197705d39f
-- title:
--   Unnumbered §II: syllable identities and equivalent generating basis
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   The syllables $a=TH$, $b=SH$ satisfy the exact projective identities
--
--   $$H=ab^2a,\qquad T=a^2b^2a,\qquad \operatorname{ord}(b)=3.$$
--
--   Moreover $\langle a,b\rangle=\langle H,T\rangle$: a projective gate has a word over either alphabet exactly when it has a word over the other. These identities transfer the established universality of the H,T basis to the syllable basis.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 2, Unnumbered §II: syllable identities and equivalent generating basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Unnumbered §II, PDF p.2. Exact projective identities transfer the
known universality of H,T; no quantitative universality claim is added. -/
theorem syllable_identities_and_basis :
    SameGate QAlgorithms.hadamard
      (syllableMatrix .th * syllableMatrix .sh ^ 2 * syllableMatrix .th) ∧
    SameGate QAlgorithms.gateT
      (syllableMatrix .th ^ 2 * syllableMatrix .sh ^ 2 * syllableMatrix .th) ∧
    SameGate (syllableMatrix .sh ^ 3) 1 ∧
    (∀ k : ℕ, 0 < k → k < 3 → ¬ SameGate (syllableMatrix .sh ^ k) 1) ∧
    (∀ U : Mat,
      (∃ w : List BsHTLetter, SameGate U (htValue w)) ↔
      (∃ w : List Syllable, SameGate U (syllableValue w))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
