-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_gaussian_unitary_mobius
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.gaussian_unitary_mobius
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:54:49.564497+00:00
-- url     : https://prove2.me/theorems/289cbee0-065e-4022-9b4a-705a5e4ab6ee
-- title:
--   Theorem A.3: Gaussian-unitary Mobius transformation
-- statement:
--   Let a real symplectic matrix $S=\begin{psmallmatrix}A&B\\C&D\end{psmallmatrix}$ have a Gaussian unitary implementer on $L^2(\mathbb R^n)$, in the convention $\widehat U^\dagger x\widehat U=Sx$. Let $\psi$ be an actual centered normalized Gaussian vector represented by valid graph $Z$. Then $A+BZ$ is invertible, $\widehat U\psi$ is Gaussian, and
--
--   $$Z'=(C+DZ)(A+BZ)^{-1},\qquad\Sigma_{Z'}=S\Sigma_ZS^T.$$
--
--   The expectation-defined graph of the output is $Z'$ and is again symmetric with positive definite imaginary part. Output physicality is a conclusion.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 20, Theorem A.3: Gaussian-unitary Mobius transformation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.20–21, Theorem A.3: Mobius law on expectation-defined
graphs of actual states under Gaussian unitaries, including output Gaussianity,
denominator invertibility, covariance congruence, and output physicality. -/
theorem gaussian_unitary_mobius {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : graphBlockSymplectic A B C D) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : ValidGraph Z)
    (psi : Schrodinger n) (hPsi : GaussianGraphRepresents Z psi)
    (Uop : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n)
    (hOp : IsImplementer (Matrix.fromBlocks A B C D) Uop) :
    IsUnit (complexify A + complexify B * Z).det ∧
    ValidGraph (mobius A B C D Z) ∧ IsGaussianVector (Uop psi) ∧
    GaussianGraphRepresents (mobius A B C D Z) (Uop psi) ∧
    graphCovariance (mobius A B C D Z) =
      (Matrix.fromBlocks A B C D) * graphCovariance Z * (Matrix.fromBlocks A B C D).transpose := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
