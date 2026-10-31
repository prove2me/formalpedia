-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_local_squeezing
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.local_squeezing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:44:07.84103+00:00
-- url     : https://prove2.me/theorems/6dbb7e36-d249-42d8-bba4-112dbbd5ed67
-- title:
--   III.E: single-mode squeezing graph rule
-- statement:
--   For a valid one-mode block graph $Z=\begin{psmallmatrix}t&r^T\\r&W\end{psmallmatrix}$ and real squeezing parameter $s$, the symplectic action $\operatorname{diag}(e^s,e^{-s})$ gives the valid graph
--
--   $$Z'=\begin{pmatrix}e^{-2s}t&e^{-s}r^T\\e^{-s}r&W\end{pmatrix}.$$
--
--   Positive $s$ squeezes momentum; negative $s$ squeezes position. Only edges incident to the active node are rescaled.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 11, III.E: single-mode squeezing graph rule

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.11, (3.16): positive s squeezes p; the connection vector is r. -/
theorem local_squeezing {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (hZ : ValidGraph (oneGraph t r W)) (s : ℝ) :
    oneAction (Real.exp s) 0 0 (Real.exp (-s)) (oneGraph t r W) =
      oneGraph ((Real.exp (-2*s) : ℂ) * t) (fun j => (Real.exp (-s) : ℂ) * r j) W ∧
    ValidGraph (oneGraph ((Real.exp (-2*s) : ℂ) * t) (fun j => (Real.exp (-s) : ℂ) * r j) W) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
