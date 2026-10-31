-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_self_inverse_hgraph
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.self_inverse_hgraph
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:40:47.092537+00:00
-- url     : https://prove2.me/theorems/9e41ce69-cc8c-4ce9-9ef8-74e3b7305315
-- title:
--   II.G: self-inverse H-graph simplification, Eq. (2.34)
-- statement:
--   Let $G$ be a finite real symmetric matrix with $G^2=I$, and let $\alpha$ be real. The H-graph coordinate is a valid Gaussian graph and has the exact expression
--
--   $$i e^{-2\alpha G}=i\cosh(2\alpha)I-i\sinh(2\alpha)G.$$
--
--   This is the self-inverse matrix-exponential simplification, without any bipartite assumption. The operator-theoretic Hamiltonian generation assertion is separately deferred.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 8, II.G: self-inverse H-graph simplification, Eq. (2.34)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.8, (2.34): exact self-inverse H-graph exponential identity;
no bipartiteness assumption occurs in this result. -/
theorem self_inverse_hgraph {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℝ) (hG : G.IsSymm) (hInv : G * G = 1) (alpha : ℝ) :
    ValidGraph (hGraph G alpha) ∧ hGraph G alpha =
      (Complex.I * (Real.cosh (2 * alpha) : ℂ)) • 1 -
      (Complex.I * (Real.sinh (2 * alpha) : ℂ)) • complexify G := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
