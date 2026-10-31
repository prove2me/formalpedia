-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_fourier_and_double_fourier
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.fourier_and_double_fourier
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:44:48.743474+00:00
-- url     : https://prove2.me/theorems/b0cbea45-05fa-43e2-aaee-318292a3cfbe
-- title:
--   III.E: Fourier and double-Fourier rules
-- statement:
--   Let $Z=\begin{psmallmatrix}t&r^T\\r&W\end{psmallmatrix}$ be valid. With the source convention $F=S_{\mathrm{phase}}(-\pi/2)$, one has $t\ne0$ and
--
--   $$F:Z\mapsto\begin{pmatrix}-t^{-1}&-t^{-1}r^T\\-t^{-1}r&W-t^{-1}rr^T\end{pmatrix},\qquad F^2:Z\mapsto\begin{pmatrix}t&-r^T\\-r&W\end{pmatrix}.$$
--
--   The second formula also holds algebraically for every finite complex block graph, including real ideal graphs with $t=0$. The single-Fourier division is never used at that ideal singularity.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 12, III.E: Fourier and double-Fourier rules

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.12, (3.20)–(3.21): F=Sphase(-pi/2) and F^2.
The F^2 polynomial formula also extends to every finite ideal graph, including t=0. -/
theorem fourier_and_double_fourier {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (hZ : ValidGraph (oneGraph t r W)) :
    t ≠ 0 ∧
    oneAction 0 (-1) 1 0 (oneGraph t r W) =
      oneGraph (-t⁻¹) (fun j => -t⁻¹ * r j) (fun j k => W j k - t⁻¹ * r j * r k) ∧
    oneAction 0 (-1) 1 0 (oneAction 0 (-1) 1 0 (oneGraph t r W)) = oneGraph t (-r) W ∧
    (∀ (t0 : ℂ) (r0 : J → ℂ) (W0 : Matrix J J ℂ),
      oneAction (-1) 0 0 (-1) (oneGraph t0 r0 W0) = oneGraph t0 (-r0) W0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
