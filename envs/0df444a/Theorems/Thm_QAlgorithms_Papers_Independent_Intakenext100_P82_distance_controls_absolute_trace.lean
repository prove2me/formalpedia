-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_distance_controls_absolute_trace
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.distance_controls_absolute_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:11:34.406985+00:00
-- url     : https://prove2.me/theorems/fc3807bf-7838-443b-bc7f-21f7a5a30eb2
-- title:
--   Unnumbered §IV: distance controls absolute trace
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   For any single-qubit unitary representatives $U,V$ and any $\epsilon>0$, with the source distance $d(U,V)=\sqrt{2-|\operatorname{tr}(UV^\dagger)|}/2$,
--
--   $$d(U,V)<\epsilon\quad\Longrightarrow\quad\bigl||\operatorname{tr}U|-|\operatorname{tr}V|\bigr|<4\epsilon.$$
--
--   Absolute traces are invariant under the choice of global phase. This implication justifies absolute trace as a primary proximity-search key.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 4, Unnumbered §IV: distance controls absolute trace

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Unnumbered §IV, PDF p.4; denominator 2 lies outside the square root. -/
theorem distance_controls_absolute_trace (U V : Mat)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (hV : V ∈ Matrix.unitaryGroup Bool ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hclose : gateDistance U V < epsilon) :
    |‖Matrix.trace U‖ - ‖Matrix.trace V‖| < 4 * epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
