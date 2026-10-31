-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_measured_second_moments
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.measured_second_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:38:37.03714+00:00
-- url     : https://prove2.me/theorems/7cb529be-20e2-4ca6-94a2-e0a25f7d04fb
-- title:
--   II.E: graph from measured second moments, Eq. (2.27)
-- statement:
--   Let $f$ be a normalized, centered, $n$-mode Gaussian wavefunction on $\mathbb R^n$, with $\hbar=1$. Let $Q_{jk}=\langle q_jq_k\rangle$, $P_{jk}=\langle q_jp_k\rangle$, and $H_{jk}=\langle q_jp_k+p_kq_j\rangle$. All first and second quadrature forms are integrable; $Q$ is positive definite and invertible, and
--
--   $$P=\tfrac12 H+\tfrac i2 I,\qquad Z=Q^{-1}P=\tfrac12 Q^{-1}(H+iI).$$
--
--   The resulting $Z$ is symmetric with positive definite imaginary part. This identifies the graph using measured second moments, with vacuum $Q=I/2$.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 7, II.E: graph from measured second moments, Eq. (2.27)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.6–7, (2.25)–(2.27): actual second-moment graph extraction.
Vacuum normalization is Q=I/2 and <qp^T>=iI/2. -/
theorem measured_second_moments {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : NormalizedGaussian f) :
    HasQuadratureForms f ∧ (realPart (qMoment f)).PosDef ∧
    IsUnit (qMoment f).det ∧
    (∀ j k, qpMoment f j k = (symQpMoment f j k / 2 : ℝ) +
      (Complex.I / 2) * (if j = k then 1 else 0)) ∧
    extractedGraph f = (1 / 2 : ℂ) • ((qMoment f)⁻¹ *
      (complexify (symQpMoment f) + Complex.I • 1)) ∧
    ValidGraph (extractedGraph f) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
