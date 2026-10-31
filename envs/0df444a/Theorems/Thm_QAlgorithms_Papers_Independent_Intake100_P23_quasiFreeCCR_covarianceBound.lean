-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_quasiFreeCCR_covarianceBound
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.quasiFreeCCR_covarianceBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:14:17.000992+00:00
-- url     : https://prove2.me/theorems/b9cb4eec-f7aa-4573-90c0-0199a6bc891c
-- title:
--   Bosonic covariance bound
-- statement:
--   Let $W$ be a Weyl representation of a real vector space $(Y,\omega)$ on a complex Hilbert space, and let $\Psi$ have the Gaussian characteristic function $\langle\Psi,W(y)\Psi\rangle=e^{-\eta(y,y)/4}$ for a symmetric real bilinear form $\eta$. Then
--   $$|\omega(y,z)|\le2\sqrt{|\eta(y,y)|}\sqrt{|\eta(z,z)|}\qquad(y,z\in Y).$$
--   This is the precise printed bound; it keeps the source's factor $2$ and does not use the inconsistent two-point normalization in clause 1.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 39, Theorem 39

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.39, Theorem 39(2): the source's factor-2 covariance estimate with (70). -/
theorem quasiFreeCCR_covarianceBound (omega eta : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hanti : Antisymmetric omega) (W : Y → H →L[ℂ] H)
    (hW : IsCCR omega W) (v : H) (hg : GaussianCharacteristic W v eta) :
    ∀ y z, |omega y z| ≤ 2 * Real.sqrt |eta y y| * Real.sqrt |eta z z| := by sorry

end QAlgorithms.Papers.Independent.Intake100.P23

end
