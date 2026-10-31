-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_pauli_propagation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.pauli_propagation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:37:51.3294+00:00
-- url     : https://prove2.me/theorems/236d66ca-567d-4899-864b-674482e483c0
-- title:
--   §3: Pauli propagation and adaptive rotation signs
-- statement:
--   Let $R_x(\theta)=e^{-i\theta X}$, $R_z(\theta)=e^{-i\theta Z}$ and $W(\theta)=H\operatorname{diag}(1,e^{i\theta})$. For every real $\theta$,
--
--   $$\begin{aligned}R_x(\theta)X&=XR_x(\theta),&R_x(\theta)Z&=ZR_x(-\theta),\\R_z(\theta)X&=XR_z(-\theta),&R_z(\theta)Z&=ZR_z(\theta),\\W(\theta)Z&=XW(\theta),&W(\theta)X&=e^{i\theta}ZW(-\theta).\end{aligned}$$
--
--   Moreover $CZ(Z\otimes I)=(Z\otimes I)CZ$ and $CZ(X\otimes I)=(X\otimes Z)CZ$, together with both swapped-wire identities. These relations determine adaptive rotation signs and Pauli propagation. The scalar omitted in the printed $W(\theta)X$ relation is retained here.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 5, §3: Pauli propagation and adaptive rotation signs

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Pauli propagation, PDF pp.5–6. The printed W(theta)X=ZW(-theta)
omits exp(i theta); that scalar is retained here. All four CZ wire cases appear. -/
theorem pauli_propagation (theta : ℝ) :
    rx theta * pauliX = pauliX * rx theta ∧
    rx theta * pauliZ = pauliZ * rx (-theta) ∧
    rz theta * pauliX = pauliX * rz (-theta) ∧
    rz theta * pauliZ = pauliZ * rz theta ∧
    wGate theta * pauliZ = pauliX * wGate theta ∧
    wGate theta * pauliX = Complex.exp (Complex.I * theta) • (pauliZ * wGate (-theta)) ∧
    controlled pauliZ * Matrix.kronecker pauliZ 1 = Matrix.kronecker pauliZ 1 * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker pauliX 1 = Matrix.kronecker pauliX pauliZ * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker 1 pauliZ = Matrix.kronecker 1 pauliZ * controlled pauliZ ∧
    controlled pauliZ * Matrix.kronecker 1 pauliX = Matrix.kronecker pauliZ pauliX * controlled pauliZ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
