-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_controlled_z_update
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.controlled_z_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:45:14.061573+00:00
-- url     : https://prove2.me/theorems/287538c9-6163-4b53-8a99-da85d0f9ece1
-- title:
--   III.E: controlled-Z adds a real edge
-- statement:
--   Let a valid graph have two distinct active modes with block $T$ and untouched blocks $R,W$. For real controlled-$Z$ strength $g$, write $E=\begin{psmallmatrix}0&g\\g&0\end{psmallmatrix}$. Then
--
--   $$Z'=\begin{pmatrix}T+E&R^T\\R&W\end{pmatrix}.$$
--
--   This remains a valid Gaussian graph. Both symmetric weights between the active nodes increase by $g$, and the diagonal self-loops do not change.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 12, III.E: controlled-Z adds a real edge

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.12, (3.22)–(3.23): two distinct active modes; add g to
both symmetric off-diagonal entries, leaving self-loops and W unchanged. -/
theorem controlled_z_update {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix (Fin 2) (Fin 2) ℂ) (R : Matrix J (Fin 2) ℂ) (W : Matrix J J ℂ)
    (hZ : ValidGraph (Matrix.fromBlocks T R.transpose R W)) (g : ℝ) :
    let C := g • twoEdge
    graphLocalMobius 1 0 C 1 (Matrix.fromBlocks T R.transpose R W) =
      Matrix.fromBlocks (T + complexify C) R.transpose R W ∧
    ValidGraph (Matrix.fromBlocks (T + complexify C) R.transpose R W) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
