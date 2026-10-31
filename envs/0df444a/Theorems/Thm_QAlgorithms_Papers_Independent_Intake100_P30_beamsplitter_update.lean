-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_beamsplitter_update
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.beamsplitter_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:42:50.883133+00:00
-- url     : https://prove2.me/theorems/b4a0dfc8-2830-49f4-8f64-0e202671fd72
-- title:
--   III.C: beamsplitter graph rule, Eqs. (3.10)–(3.12)
-- statement:
--   Let $Z=\begin{psmallmatrix}T&R^T\\R&W\end{psmallmatrix}$ be valid with two active modes. For real $\theta$, let $O=\begin{psmallmatrix}\cos\theta&-\sin\theta\\\sin\theta&\cos\theta\end{psmallmatrix}$. The source's beamsplitter has amplitude reflectivity $\sin\theta$, and gives
--
--   $$Z'=\begin{pmatrix}OTO^T&OR^T\\RO^T&W\end{pmatrix}.$$
--
--   Writing $H=OTO^T$, its active entries are $H_{11}=T_{11}\cos^2\theta+T_{22}\sin^2\theta-T_{12}\sin2\theta$, $H_{12}=T_{12}\cos2\theta+\tfrac12(T_{11}-T_{22})\sin2\theta$, and $H_{22}=T_{22}\cos^2\theta+T_{11}\sin^2\theta+T_{12}\sin2\theta$. The output remains valid, and the formula includes the 50:50 case $\theta=\pi/4$.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 10, III.C: beamsplitter graph rule, Eqs. (3.10)–(3.12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.10,12–13, (3.10)–(3.12): beamsplitter with amplitude
reflectivity sin theta and the specified orientation, including the active entries. -/
theorem beamsplitter_update {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix (Fin 2) (Fin 2) ℂ) (R : Matrix J (Fin 2) ℂ) (W : Matrix J J ℂ)
    (hZ : ValidGraph (Matrix.fromBlocks T R.transpose R W)) (theta : ℝ) :
    let O := beamRotation theta
    let H := complexify O * T * (complexify O).transpose
    ValidGraph (graphLocalMobius O 0 0 O (Matrix.fromBlocks T R.transpose R W)) ∧
    graphLocalMobius O 0 0 O (Matrix.fromBlocks T R.transpose R W) =
      Matrix.fromBlocks H (complexify O * R.transpose) (R * (complexify O).transpose) W ∧
    H 0 0 = T 0 0 * (Real.cos theta : ℂ)^2 + T 1 1 * (Real.sin theta : ℂ)^2 -
      T 0 1 * (Real.sin (2 * theta) : ℂ) ∧
    H 0 1 = T 0 1 * (Real.cos (2 * theta) : ℂ) +
      (1 / 2 : ℂ) * (T 0 0 - T 1 1) * (Real.sin (2 * theta) : ℂ) ∧
    H 1 1 = T 1 1 * (Real.cos theta : ℂ)^2 + T 0 0 * (Real.sin theta : ℂ)^2 +
      T 0 1 * (Real.sin (2 * theta) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
