-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P24_fidelityDistance
-- name    : QAlgorithms.Papers.Independent.Support50.P24.fidelityDistance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:02:14.01998+00:00
-- url     : https://prove2.me/theorems/72aa63ee-35b4-481c-9172-6fcf958a1cff
-- title:
--   Refocusing distance determines squared qubit channel fidelity
-- statement:
--   Let $U_{\rm in},U_{\rm out}\in\mathrm{SU}(2)$. For matrices $A$, use the source convention $\|A\|=\sqrt{\operatorname{Tr}(A^\dagger A)}/2$. Let $F_{\rm ch}$ denote squared fidelity of the normalized Choi states of two unitary channels. Then
--
--   $$F_{\rm ch}(U_{\rm out},U_{\rm in}^\dagger)
--   =\frac{|\operatorname{Tr}(U_{\rm out}^\dagger U_{\rm in}^\dagger)|^2}{4}
--   =\left(1-\|U_{\rm out}U_{\rm in}-I\|^2\right)^2.$$
--
--   There is no nonnegative-scalar-part restriction on $U_{\rm out}U_{\rm in}$. In particular the formula also covers $U_{\rm out}U_{\rm in}=-I$. This identity compares the paper's refocusing error convention with channel fidelity.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, PDF p. 26, Unnumbered identity on p.26: normalized Hilbert–Schmidt distance and qubit channel fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24

noncomputable section

open QAlgorithms MeasureTheory

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P24.groupedContinuousENorm

/-- PDF pp.25-26: squared normalized-Choi fidelity equals the square of one minus
squared refocusing distance. No sign restriction on the scalar part of Uout Uin is imposed. -/
theorem fidelityDistance
    (Uin Uout : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    qubitChannelFidelity Uout.val Uin.valᴴ =
      (1 - refocusingNorm (Uout.val * Uin.val - 1)^2)^2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P24

end
