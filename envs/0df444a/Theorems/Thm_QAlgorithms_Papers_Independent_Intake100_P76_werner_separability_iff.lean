-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_werner_separability_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.werner_separability_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:28:07.566327+00:00
-- url     : https://prove2.me/theorems/f52e25ed-f97d-43db-bbf9-d0292f847af2
-- title:
--   Werner separability threshold
-- statement:
--   Let $0<x<1$ and let $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ in the computational basis of $\mathbb C^2\otimes\mathbb C^2$. The operator $\rho_w(x)=(1-x)I_4/4+x|\Psi^-\rangle\langle\Psi^-|$ is a density matrix, and
--
--   $$\rho_w(x)\text{ is separable}\iff x\leq\frac13.$$
--
--   This includes the separability boundary and characterizes precisely the family displayed in Eq. (14).
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 3, Eq. (14), unnumbered: Werner-state separability threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.3, Eq. (14) and following sentence: separability of the printed
Werner family, including the boundary x=1/3 within its open parameter domain. -/
theorem werner_separability_iff (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    IsDensityMatrix (wernerDensity x) ∧
      (IsSeparableDensity (wernerDensity x) ↔ x ≤ 1 / 3) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
