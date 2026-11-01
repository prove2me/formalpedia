-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_averageCoherentFidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.averageCoherentFidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:21:33.008347+00:00
-- url     : https://prove2.me/theorems/d8313cd8-db08-40d5-b721-a4a6796d75ff
-- title:
--   Average Gaussian-prior coherent-state fidelity
-- statement:
--   Let $\lambda>0$, $\tau\ge0$, and let $\Phi$ be a zero-displacement phase-insensitive Gaussian channel with noise $y\ge|1-\tau|$ on the complete oscillator space. The coherent projectors are normalized trace-class states, their channel outputs have bounded operator realizations, and the prior $P_\lambda(\alpha)=(\lambda/\pi)e^{-\lambda|\alpha|^2}$ is integrable with integral one. Pointwise,
--
--   $$\langle\alpha|\Phi(|\alpha\rangle\langle\alpha|)|\alpha\rangle=\frac{2\exp\!\left[-2(1-\sqrt\tau)^2|\alpha|^2/(1+y+\tau)\right]}{1+y+\tau}.$$
--
--   The prior-weighted overlap is integrable and
--
--   $$\overline F_\lambda=\int_{\mathbb C}P_\lambda(\alpha)\langle\alpha|\Phi(|\alpha\rangle\langle\alpha|)|\alpha\rangle\,d^2\alpha=\frac{2\lambda}{2(1-\sqrt\tau)^2+\lambda(1+y+\tau)}.$$
--
--   This is squared pure-state fidelity. The source's $Q_{\Phi(|\alpha\rangle\langle\alpha|)}(\alpha)$ is the pointwise overlap divided by $\pi$, including dependence on $\alpha$ through the input state. No resource-entanglement assumption is needed for this channel identity.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 4, Average coherent-state fidelity of a physical phase-insensitive channel, Eq. (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.4, (11)--(12): actual squared-overlap integral and pointwise
Q/overlap identity. Integrability, prior normalization, coherent normalization
and bounded output realization are conclusions, not assumed formulae. -/
theorem averageCoherentFidelity (lambda tau y : ℝ) (Phi : OscillatorChannel)
    (hlambda : 0 < lambda) (htau : 0 ≤ tau) (hPhi : PhaseInsensitive Phi tau y) :
    CoherentRealized ∧
    Integrable (priorDensity lambda) ∧ (∫ alpha : ℂ, priorDensity lambda alpha) = 1 ∧
    (∀ alpha : ℂ, IsDensity (coherentKernel alpha) ∧
      HasFockMatrix (operatorOfMatrix (Phi (coherentKernel alpha))) (Phi (coherentKernel alpha)) ∧
      teleportedCoherentOverlap Phi alpha =
        2 * Real.exp (-2 * (1 - Real.sqrt tau) ^ 2 * Complex.normSq alpha / (1 + y + tau)) /
          (1 + y + tau)) ∧
    Integrable (fun alpha => priorDensity lambda alpha * teleportedCoherentOverlap Phi alpha) ∧
    gaussianPriorFidelity lambda Phi = phaseInsensitiveFidelityFormula lambda tau y := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
