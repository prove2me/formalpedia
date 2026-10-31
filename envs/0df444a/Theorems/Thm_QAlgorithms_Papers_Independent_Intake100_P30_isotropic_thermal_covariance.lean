-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_isotropic_thermal_covariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.isotropic_thermal_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:56:30.77636+00:00
-- url     : https://prove2.me/theorems/38662bd3-2699-4484-9363-d1899e5ee831
-- title:
--   Appendix D: equal-thermal-noise covariance extension
-- statement:
--   Let $S$ be a finite real symplectic matrix in grouped quadrature order and let $\kappa\ge1$ be the common thermal parameter in Eq. (D1). With vacuum covariance $I/2$, the covariance is
--
--   $$\Sigma=\tfrac12S\operatorname{diag}(\kappa I,\kappa I)S^T=\kappa\,\tfrac12SS^T.$$
--
--   Its symplectic eigenvalues are all $\kappa/2$. There exists a valid graph $Z$ with $\Sigma=\kappa\Sigma_Z$, recovered by applying pure covariance extraction to $\Sigma/\kappa$. This states the explicit equal-thermal-noise covariance extension and fixes the paper's adjacent inconsistent uses of the word eigenvalue.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 24, Appendix D: equal-thermal-noise covariance extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.24, (D1): common thermal parameter kappa scales the pure
covariance and gives actual symplectic eigenvalues kappa/2. The physical
convention is kappa>=1, and the graph is that of Sigma/kappa. -/
theorem isotropic_thermal_covariance (n : ℕ) (kappa : ℝ) (hKappa : 1 ≤ kappa)
    (A B C D : Matrix (Fin n) (Fin n) ℝ) (hS : graphBlockSymplectic A B C D) :
    let S := Matrix.fromBlocks A B C D
    let Sigma := (1/2 : ℝ) • (S * Matrix.fromBlocks (kappa • 1) 0 0 (kappa • 1) * S.transpose)
    Sigma = kappa • ((1/2 : ℝ) • (S * S.transpose)) ∧
    HasSymplecticSpectrum Sigma (fun _ => kappa/2) ∧
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, ValidGraph Z ∧
      Sigma = kappa • graphCovariance Z ∧ covarianceGraph (kappa⁻¹ • Sigma) = Z := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
