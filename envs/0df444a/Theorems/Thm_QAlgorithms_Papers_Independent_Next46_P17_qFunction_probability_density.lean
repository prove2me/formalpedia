-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_qFunction_probability_density
-- name    : QAlgorithms.Papers.Independent.Next46.P17.qFunction_probability_density
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:30:44.192686+00:00
-- url     : https://prove2.me/theorems/0cab8887-8ea3-42df-99ee-e7aaaf1ab9ad
-- title:
--   Appendix: qFunction probability density
-- statement:
--   Let $n\geq1$ and let $\rho$ be a normalized full $n$-mode state. Define $D(\eta)=e^{i\eta\cdot JR}$ and $\chi_\rho(\eta)=\operatorname{tr}(D(\eta)\rho)$. With Lebesgue measure on $\mathbb R^{2n}$, set
--
--   $$
--   Q_\rho(\xi)=\frac{1}{(2\pi)^{2n}}\operatorname{Re}\int e^{i\xi\cdot J\eta}\chi_\rho(\eta)e^{-\|\eta\|^2/4}\,d\eta.
--   $$
--
--   Then $Q_\rho$ is integrable and
--
--   $$
--   Q_\rho(\xi)\geq0\quad\text{for all }\xi,\qquad \int Q_\rho(\xi)\,d\xi=1.
--   $$
--
--   Thus the exact Fourier-Gaussian Q function in (100) is a probability density, independently of the separate coherent-label discrepancy.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 13, Appendix, probability density after (100)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.13, Appendix: the Fourier Q function (100) is a probability density.
Integrability is asserted, not left to a default-zero integral. The separate
coherent-label identity and inverse-Q distributional kernel are not asserted. -/
theorem qFunction_probability_density {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) :
    Integrable (qFunction rho.coefficients) ∧
    (∀ xi : InterleavedPhaseVector n, 0 ≤ qFunction rho.coefficients xi) ∧
    (∫ xi : InterleavedPhaseVector n, qFunction rho.coefficients xi) = 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
