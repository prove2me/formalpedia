-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_multimode_entropy_power
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.multimode_entropy_power
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:06:00.042776+00:00
-- url     : https://prove2.me/theorems/0a84c0ec-77fa-4bb9-b295-692cf92bb5bd
-- title:
--   Section II, Eq.(9): multi-mode quantum entropy power inequality
-- statement:
--   Let $n,K\ge1$ and let $\Phi$ be a Gaussian linear scattering channel on $K$ independent $n$-mode bosonic subsystems, with real blocks $M_\alpha$ satisfying $\sum_\alpha M_\alpha\Delta M_\alpha^T=\Delta$. Each input $\rho_\alpha$ is an arbitrary normalized positive trace-class density on the full completed $n$-mode number-basis Hilbert space; correlations within a subsystem are allowed. Write $\rho_Y=\Phi(\bigotimes_\alpha\rho_\alpha)$, $S(\rho)=-\operatorname{Tr}\rho\ln\rho$ in nats, and $\lambda_\alpha=|\det M_\alpha|^{1/n}$. Then
--
--   $$e^{S(\rho_Y)/n}\ge\sum_\alpha\lambda_\alpha e^{S(\rho_\alpha)/n}.$$
--
--   Entropy and entropy power retain $+\infty$, with a zero-weight term interpreted as zero. No finite-energy, Gaussian-input, or energy-preservation restriction is imposed. This is the multi-mode qEPI itself.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 3, Section II, Eq.(9): multi-mode quantum entropy power inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF p.3, Section II, (9): multi-mode qEPI for arbitrary density inputs.
Entropy is in nats and retains infinity. ENNReal multiplication makes a singular
block contribute zero even when that input has infinite entropy. -/
theorem multimode_entropy_power {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n)) :
    (∑ a, ENNReal.ofReal (determinantWeight (C.block a)) *
      bosonicEntropyPower n (extendedEntropyNats (rho a).coefficients)) ≤
    bosonicEntropyPower n (extendedEntropyNats
      (C.channel (independentInput (fun a => (rho a).coefficients)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
