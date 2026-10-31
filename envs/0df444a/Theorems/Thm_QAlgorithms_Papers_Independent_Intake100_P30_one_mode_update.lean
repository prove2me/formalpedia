-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_one_mode_update
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.one_mode_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:42:27.361818+00:00
-- url     : https://prove2.me/theorems/53ff2b79-1225-4e72-b4c7-d55bf4938a96
-- title:
--   III.B: one-mode Gaussian graph update, Eq. (3.9)
-- statement:
--   Let $Z=\begin{psmallmatrix}t&r^T\\r&W\end{psmallmatrix}$ be a valid Gaussian graph with one distinguished mode, and let real $a,b,c,d$ satisfy $ad-bc=1$. The denominator $a+bt$ is nonzero and the valid updated graph is
--
--   $$Z'=\begin{pmatrix}(c+dt)/(a+bt)&r^T/(a+bt)\\r/(a+bt)&W-brr^T/(a+bt)\end{pmatrix}.$$
--
--   The vector $r$ records connections to the remaining modes. This is the one-mode specialization of the Gaussian graph transformation.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 10, III.B: one-mode Gaussian graph update, Eq. (3.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.9–10, (3.9): one-mode specialization; ad-bc=1 is symplecticity. -/
theorem one_mode_update {J : Type*} [Fintype J] [DecidableEq J]
    (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) (a b c d : ℝ)
    (hZ : ValidGraph (oneGraph t r W)) (hS : a * d - b * c = 1) :
    (a : ℂ) + (b : ℂ) * t ≠ 0 ∧
    ValidGraph (oneAction a b c d (oneGraph t r W)) ∧
    oneAction a b c d (oneGraph t r W) =
      oneGraph (((c : ℂ) + (d : ℂ) * t) / ((a : ℂ) + (b : ℂ) * t))
        (fun j => r j / ((a : ℂ) + (b : ℂ) * t))
        (fun j k => W j k - (b : ℂ) * r j * r k / ((a : ℂ) + (b : ℂ) * t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
