-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_local_shear
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.local_shear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:43:43.200497+00:00
-- url     : https://prove2.me/theorems/14515f0c-f740-48bb-b718-0814129ca856
-- title:
--   III.E: local shear changes only a self-loop
-- statement:
--   For a valid graph $Z=\begin{psmallmatrix}t&r^T\\r&W\end{psmallmatrix}$ and any real shear strength $g$, the local symplectic shear $\begin{psmallmatrix}1&0\\g&1\end{psmallmatrix}$ gives
--
--   $$Z'=\begin{pmatrix}t+g&r^T\\r&W\end{pmatrix}.$$
--
--   The graph stays valid. Only the real self-loop on the active node changes; its links and the rest of the graph remain as displayed.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 11, III.E: local shear changes only a self-loop

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.11, (3.14): local shear changes just one real self-loop. -/
theorem local_shear {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (hZ : ValidGraph (oneGraph t r W)) (g : ℝ) :
    oneAction 1 0 g 1 (oneGraph t r W) = oneGraph (t + (g : ℂ)) r W ∧
    ValidGraph (oneGraph (t + (g : ℂ)) r W) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
