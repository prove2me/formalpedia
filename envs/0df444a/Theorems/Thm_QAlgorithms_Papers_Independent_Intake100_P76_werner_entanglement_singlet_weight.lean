-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_werner_entanglement_singlet_weight
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.werner_entanglement_singlet_weight
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:29:46.030982+00:00
-- url     : https://prove2.me/theorems/4c1a3885-c81c-43aa-b8b6-59fd11f2bcb4
-- title:
--   Werner BSA entanglement equals its singlet weight
-- statement:
--   For $0<x<1$, let $\rho_w(x)=(1-x)I_4/4+x|\Psi^-\rangle\langle\Psi^-|$, where $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$. Let $\lambda(x)$ be its optimal separable trace and $E_{\mathrm{BSA}}$ the functional of Eqs. (12)–(13), using base-two entropy. Then
--
--   $$E_{\mathrm{BSA}}(\rho_w(x))=1-\lambda(x),\qquad S_2\!\left(\operatorname{Tr}_B|\Psi^-\rangle\langle\Psi^-|\right)=S_2\!\left(\operatorname{Tr}_A|\Psi^-\rangle\langle\Psi^-|\right)=1.$$
--
--   The entanglement value is measured in ebits, and the equality concerns this paper's BSA functional.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 4, After Eq. (16): Werner BSA entanglement equals singlet weight

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.4, after Eq. (16): the BSA entanglement of a Werner state is the
singlet weight in ebits, since either singlet reduction has entropy one bit. -/
theorem werner_entanglement_singlet_weight (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    bsaEntanglement (wernerDensity x) = 1 - bsaWeight (wernerDensity x) ∧
      vnEntropy (traceRight (QAlgorithms.Papers.Independent.Dependency50.P06.singlet)) = 1 ∧
      vnEntropy (traceLeft (QAlgorithms.Papers.Independent.Dependency50.P06.singlet)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
