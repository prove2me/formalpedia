-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_gaussian_graph_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.gaussian_graph_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:53:19.860816+00:00
-- url     : https://prove2.me/theorems/34557e04-6693-43de-af2c-812fa57affee
-- title:
--   Theorem A.1: graph symmetry, uniqueness and positive imaginary part
-- statement:
--   Let $\psi$ be a normalized centered $n$-mode Gaussian pure state in the full Schrödinger Hilbert space $L^2(\mathbb R^n)$. Its norm is one, and there exists exactly one graph extracted from its quadrature second moments that represents it:
--
--   $$Z=\langle qq^T\rangle^{-1}\langle qp^T\rangle,\qquad Z^T=Z,\qquad\operatorname{Im}Z>0.$$
--
--   Representing a vector means using an almost-everywhere equal normalized Gaussian wavefunction to evaluate these moments. This gives graph uniqueness for an actual state, rather than defining states as graph parameters.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 19, Theorem A.1: graph symmetry, uniqueness and positive imaginary part

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.19–20, Theorem A.1: every actual centered normalized
Gaussian vector has a unique valid expectation-defined graph. The state is an
L2 vector; it is not defined to be a covariance or a graph. -/
theorem gaussian_graph_unique {n : ℕ} (psi : Schrodinger n)
    (hPsi : IsGaussianVector psi) :
    ‖psi‖ = 1 ∧ ∃! Z : Matrix (Fin n) (Fin n) ℂ, ValidGraph Z ∧ GaussianGraphRepresents Z psi := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
