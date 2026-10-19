-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_qubit_observational_and_incoherent_ergotropies
-- name    : QAlgorithms.Papers.Independent.Information100.P38.qubit_observational_and_incoherent_ergotropies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:11:31.950689+00:00
-- url     : https://prove2.me/theorems/e4c240f1-74a3-4d71-9bad-44f26eacc571
-- title:
--   Appendix B
-- statement:
--   Let $H=E|1\rangle\langle1|$, $E>0$, let $\rho=(I+\mathbf v\cdot\boldsymbol\sigma)/2$ with $|\mathbf v|\le1$, and let $M_\pm=(I\pm\mathbf m\cdot\boldsymbol\sigma)/2$ with $|\mathbf m|=1$. Then $\rho$ is a density matrix and $M$ a POVM, and
--
--   $$E_O(\rho,M)=\frac E2\bigl(|\mathbf v\cdot\mathbf m|-v_z\bigr),\qquad E_{\rm inc}(\rho)=\frac E2\bigl(|v_z|-v_z\bigr).$$
--
--   The Pauli convention is $\sigma_y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$ and $v_z=\rho_{00}-\rho_{11}$, so $|0\rangle$ is the ground state. The formulas specify the two ergotropies themselves, before taking any state optimization.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 12, Appendix B

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.12, Appendix B: both explicit ergotropy formulas for arbitrary qubit
states and rank-one projective measurements, with H=E|1><1| and n_z=rho_00-rho_11. -/
theorem qubit_observational_and_incoherent_ergotropies (E : ℝ) (hE : 0 < E)
    (v m : Fin 3 → ℝ) (hv : ergotropicBlochLengthSquared v ≤ 1)
    (hm : ergotropicBlochLengthSquared m = 1) :
    IsDensityMatrix (ergotropicBlochMatrix v) ∧ IsPOVM (ergotropicBlochMeasurement m) ∧
    observationalErgotropy ![0, E] (ergotropicBlochMeasurement m) (ergotropicBlochMatrix v) =
      E / 2 * (|ergotropicBlochDot v m| - v 2) ∧
    incoherentErgotropy ![0, E] (ergotropicBlochMatrix v) = E / 2 * (|v 2| - v 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
