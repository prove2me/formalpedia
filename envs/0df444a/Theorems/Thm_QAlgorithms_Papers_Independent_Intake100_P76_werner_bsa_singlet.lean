-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_werner_bsa_singlet
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.werner_bsa_singlet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:29:07.878989+00:00
-- url     : https://prove2.me/theorems/999b62d1-946a-4af7-8ee4-1cf7562597c3
-- title:
--   The optimal Werner remainder is the weighted singlet
-- statement:
--   Let $0<x<1$, $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$, and $\rho_w(x)=(1-x)I_4/4+x|\Psi^-\rangle\langle\Psi^-|$. Let $S_*$ be the selected unrestricted BSA and $\lambda(x)=\operatorname{Tr}S_*$. The selected operator is an actual optimizer, and there exists a normalized separable density matrix $\sigma$ with $S_*=\lambda(x)\sigma$ and
--
--   $$\rho_w(x)=\lambda(x)\sigma+(1-\lambda(x))|\Psi^-\rangle\langle\Psi^-|.$$
--
--   For $x\leq1/3$, $\lambda(x)=1$ and $\rho_w(x)=\sigma$; for $x>1/3$, $0\leq\lambda(x)<1$. This identifies the optimal residual, without introducing an additional piecewise formula for the weight.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 4, Eq. (16): Werner BSA remainder is the singlet

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.4, Eq. (16): the optimal Werner remainder is the weighted singlet.
The separable weight is the computed optimal trace; no extra formula for it
is added. A normalized separable component exists also when its weight is zero. -/
theorem werner_bsa_singlet (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    IsBSA (wernerDensity x) (bsaRepresentative (wernerDensity x)) ∧
      ∃ sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        IsDensityMatrix sigma ∧ IsSeparableDensity sigma ∧
        bsaRepresentative (wernerDensity x) = (bsaWeight (wernerDensity x) : ℂ) • sigma ∧
        wernerDensity x = (bsaWeight (wernerDensity x) : ℂ) • sigma +
          ((1 - bsaWeight (wernerDensity x) : ℝ) : ℂ) • QAlgorithms.Papers.Independent.Dependency50.P06.singlet ∧
        (x ≤ 1 / 3 → bsaWeight (wernerDensity x) = 1 ∧ wernerDensity x = sigma) ∧
        (1 / 3 < x → 0 ≤ bsaWeight (wernerDensity x) ∧
          bsaWeight (wernerDensity x) < 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
