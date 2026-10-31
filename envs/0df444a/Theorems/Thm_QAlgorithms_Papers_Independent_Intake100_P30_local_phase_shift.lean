-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_local_phase_shift
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.local_phase_shift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:44:29.551948+00:00
-- url     : https://prove2.me/theorems/b8a41239-1e8b-407a-bae7-1d6cdc9c6afa
-- title:
--   III.E: local phase shift graph rule
-- statement:
--   For a valid one-mode block graph $Z=\begin{psmallmatrix}t&r^T\\r&W\end{psmallmatrix}$ and real $\theta$, put $d=\cos\theta+t\sin\theta$. Then $d\ne0$, and the source's phase rotation $\begin{psmallmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{psmallmatrix}$ gives
--
--   $$Z'=\begin{pmatrix}(-\sin\theta+t\cos\theta)/d&r^T/d\\r/d&W-\sin\theta\,rr^T/d\end{pmatrix}.$$
--
--   The output is valid. The neighborhood block can acquire new links through this operation.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 12, III.E: local phase shift graph rule

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.11–12, (3.18): the source's signed phase-shift rule. -/
theorem local_phase_shift {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (hZ : ValidGraph (oneGraph t r W)) (theta : ℝ) :
    let den : ℂ := (Real.cos theta : ℂ) + t * (Real.sin theta : ℂ)
    den ≠ 0 ∧
    oneAction (Real.cos theta) (Real.sin theta) (-Real.sin theta) (Real.cos theta) (oneGraph t r W) =
      oneGraph ((-(Real.sin theta : ℂ) + t * (Real.cos theta : ℂ)) / den)
        (fun j => r j / den)
        (fun j k => W j k - (Real.sin theta : ℂ) * r j * r k / den) ∧
    ValidGraph (oneAction (Real.cos theta) (Real.sin theta) (-Real.sin theta) (Real.cos theta)
      (oneGraph t r W)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
