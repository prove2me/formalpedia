-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_nlocal_block_update
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.nlocal_block_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:41:53.99414+00:00
-- url     : https://prove2.me/theorems/0a465ef3-a1f5-4f1d-bc20-68de718c5ff5
-- title:
--   III.A: n-local block transformation, Eq. (3.7)
-- statement:
--   Let $Z=\begin{psmallmatrix}T&R^T\\R&W\end{psmallmatrix}$ be a valid Gaussian graph on disjoint finite active and untouched mode sets. Let $S=\begin{psmallmatrix}A&B\\C&D\end{psmallmatrix}$ be real symplectic on the active modes, and put $K=A+BT$. Then $K$ is invertible, the transformed graph is valid, and
--
--   $$Z'=\begin{pmatrix}(C+DT)K^{-1}&K^{-T}R^T\\ RK^{-1}&W-RK^{-1}BR^T\end{pmatrix}.$$
--
--   Here $R$ is rectangular. The formula isolates the induced transformation of active modes and its effect through their connections to the untouched modes.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 9, III.A: n-local block transformation, Eq. (3.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.9, (3.7): n-local update, including denominator invertibility
and validity of the result as conclusions, with rectangular connecting block. -/
theorem nlocal_block_update {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (T : Matrix I I ℂ) (R : Matrix J I ℂ)
    (W : Matrix J J ℂ) (A B C D : Matrix I I ℝ)
    (hZ : ValidGraph (Matrix.fromBlocks T R.transpose R W)) (hS : graphBlockSymplectic A B C D) :
    let K := complexify A + complexify B * T
    IsUnit K.det ∧
    ValidGraph (graphLocalMobius A B C D (Matrix.fromBlocks T R.transpose R W)) ∧
    graphLocalMobius A B C D (Matrix.fromBlocks T R.transpose R W) =
      Matrix.fromBlocks (mobius A B C D T) (K⁻¹.transpose * R.transpose)
        (R * K⁻¹) (W - R * K⁻¹ * complexify B * R.transpose) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
