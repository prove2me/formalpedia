-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_twoPauli_not_degradable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.twoPauli_not_degradable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:33:23.37888+00:00
-- url     : https://prove2.me/theorems/ecee5536-35ab-43fb-8b93-346a0f70c769
-- title:
--   Two-Pauli Channels are Special: nondegradability on the whole open noise interval
-- statement:
--   Let $0<p<1$ and let $\mathcal N_p(\rho)=(1-p)\rho+\frac p2X\rho X+\frac p2Z\rho Z$ be the equal two-Pauli qubit channel. Fix its three-dimensional environment by the Stinespring matrix $U_p=\sqrt{p/2}\,X\otimes|0\rangle+\sqrt{p/2}\,Z\otimes|1\rangle+\sqrt{1-p}\,I\otimes|2\rangle$. The receiver and complementary maps are the two partial traces of this same isometry. Then
--
--   $$
--   U_p^\dagger U_p=I,\qquad \operatorname{Tr}_E(U_p\rho U_p^\dagger)=\mathcal N_p(\rho),\qquad \nexists\text{ CPTP }D:B\to E:\ D\circ\mathcal N_p=\mathcal N_p^C.
--   $$
--
--   This establishes nondegradability throughout the open noise interval, including $p=1/2$. Equality of channels is equality on every operator, so the statement includes arbitrary reference systems.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 4, Two-Pauli Channels are Special: nondegradability on the whole open noise interval

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF pp.3--4, Two-Pauli Channels are Special: not degradable
for the WHOLE interval 0<p<1. The printed inverse omits p=1/2 and the printed
D has two inconsistent signs; neither candidate D is used as a definition.
At p=1/2 the receiver kills Y while this complement does not. -/
theorem twoPauli_not_degradable (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    QAlgorithms.Papers.Independent.Information100.P67.IsIsometry (twoPauliDilation p) ∧
    QAlgorithms.Papers.Independent.Information100.P67.receiverChannel (twoPauliDilation p) = twoPauliChannel p ∧
    ¬ QAlgorithms.Papers.Independent.Information100.P67.IsDegradable (twoPauliDilation p) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
