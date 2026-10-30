-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_thermal_entropy_asymptotics
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.thermal_entropy_asymptotics
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:12:44.833431+00:00
-- url     : https://prove2.me/theorems/09466faf-b7f5-45b3-974f-84218d57520f
-- title:
--   Section III C.1, following Eq.(33): scalar thermal entropy expansion
-- statement:
--   For real $\nu\ge1$, define the scalar thermal entropy in nats by $h(\nu)=\frac{\nu+1}{2}\ln\frac{\nu+1}{2}-\frac{\nu-1}{2}\ln\frac{\nu-1}{2}$, with $0\ln0=0$. There exist constants $C>0$ and $N\ge1$ such that for every $\nu\ge N$,
--
--   $$\left|h(\nu)-\left(\ln\frac\nu2+1\right)\right|\le\frac C{\nu^2}.$$
--
--   Thus $h(\nu)=\ln(\nu/2)+1+O(\nu^{-2})$ at positive infinity. This scalar expansion needs no state, mode count, or scattering channel.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 5, Section III C.1, following Eq.(33): scalar thermal entropy expansion

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

/-- PDF p.5, following (33): h(nu)=log(nu/2)+1+O(nu^(-2)).
Positive thresholds keep every reciprocal and logarithm in its source domain. -/
theorem thermal_entropy_asymptotics :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 1 ≤ N ∧ ∀ nu : ℝ, N ≤ nu →
      |symplecticEntropy nu - (Real.log (nu / 2) + 1)| ≤ C / nu ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
