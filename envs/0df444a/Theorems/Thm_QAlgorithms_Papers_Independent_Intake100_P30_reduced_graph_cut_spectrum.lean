-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_reduced_graph_cut_spectrum
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.reduced_graph_cut_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:51:55.522785+00:00
-- url     : https://prove2.me/theorems/3b55c6fc-43f1-4e02-96ab-6b61807eda4a
-- title:
--   IV.G: reduced symplectic spectrum from graph cut
-- statement:
--   Let $V$ be a real symmetric graph on $N$ modes, let $r\in\mathbb R$, and let $s$ injectively select $n$ modes. Reduce the covariance of the actual canonical Gaussian wavefunction with graph $V+i e^{-2r}I$ to the selected coordinates. Define the positive semidefinite cut matrix
--
--   $$K_{ij}=\sum_{k\notin\operatorname{range}s}V_{s(i),k}V_{s(j),k}.$$
--
--   If $\lambda_j=\nu_j^2$ are its ordinary Hermitian eigenvalues, the reduced symplectic eigenvalues, with multiplicities, are
--
--   $$\sigma_j=\tfrac12\sqrt{1+e^{4r}\lambda_j}.$$
--
--   The reduced covariance is positive definite. Its symplectic characteristic polynomial is $\prod_j(X^2+\sigma_j^2)$, including the empty product for the empty subsystem. This is the graph-derived spectrum; no arbitrary orthogonal selector is substituted.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 17, IV.G: reduced symplectic spectrum from graph cut

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.17–18, (4.36)–(4.39): reduced covariance from a genuine
coordinate selector and its full symplectic spectrum, with multiplicities.
The Hermitian cut-matrix eigenvalues, not arbitrary supplied numbers, determine
nu_j^2. Actual Gaussian wave covariances are tied to the matrix calculation. -/
theorem reduced_graph_cut_spectrum (N n : ℕ) (select : Fin n ↪ Fin N)
    (V : Matrix (Fin N) (Fin N) ℝ) (hV : V.IsSymm) (r : ℝ) :
    let Z := canonicalGraph V r
    let P : Phase n → Phase N := Sum.map select select
    let S := (graphCovariance Z).submatrix P P
    let K : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      ∑ k : Fin N, if k ∈ Set.range select then 0 else V (select i) k * V (select j) k
    waveCovariance (gaussianWave ((Real.exp (-2*r)) • 1) (-V)) =
      graphCovariance Z ∧ S.PosDef ∧ K.PosSemidef ∧
    ∃ hK : K.IsHermitian,
      HasSymplecticSpectrum S (fun j => Real.sqrt (1 + Real.exp (4*r) * hK.eigenvalues j) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
