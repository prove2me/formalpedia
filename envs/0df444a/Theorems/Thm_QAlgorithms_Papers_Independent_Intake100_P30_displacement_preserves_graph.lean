-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_displacement_preserves_graph
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.displacement_preserves_graph
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:43:10.715327+00:00
-- url     : https://prove2.me/theorems/bfda7115-5c80-4469-bc1b-578781364e77
-- title:
--   III.E: displacement leaves the graph unchanged
-- statement:
--   Let $f$ be a normalized centered Gaussian wavefunction and $z=(d,p)$ a real phase-space displacement. Its Weyl-displaced function is $g(q)=e^{ip\cdot(q-d/2)}f(q-d)$. It remains normalized, has integrable first and second quadrature forms, has first moment $z$, and satisfies
--
--   $$\Sigma_g=\Sigma_f,\qquad Z_{\mathrm{centered}}(g)=Z_{\mathrm{centered}}(f)=Z(f).$$
--
--   Thus the graph is unchanged by displacement. Centering is essential on the displaced state; the uncentered expectation formula applies to the original centered representative.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 11, III.E: displacement leaves the graph unchanged

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.11: displacement preserves centered moments and hence the graph.
The uncentered extraction is only asserted equal on the centered input. -/
theorem displacement_preserves_graph {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : NormalizedGaussian f) (z : Phase n → ℝ) :
    let g := displacedFunction z f
    NormalizedWave g ∧ HasQuadratureForms g ∧
    (∀ a, waveMean g a = z a) ∧
    waveCovariance g = waveCovariance f ∧
    centeredGraph g = centeredGraph f ∧ centeredGraph f = extractedGraph f := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
