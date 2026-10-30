-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_entropy_rate_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.entropy_rate_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:16:15.635989+00:00
-- url     : https://prove2.me/theorems/3f2fffcf-4162-4e02-a273-c4d70734bfb2
-- title:
--   Section III C.3: limiting value of the entropy-power ratio
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian scattering channel, and let its independent normalized full $n$-mode inputs have finite mean photon number. Assume at least one block $M_\alpha$ is nonsingular. Use $\lambda_\alpha=|\det M_\alpha|^{1/n}$, the source input noises, and any global clocks satisfying the entropy clock equations. Then
--
--   $$\lim_{\tau\to\infty}\frac{\sum_\alpha\lambda_\alpha\exp(S_\alpha(\tau)/n)}{\exp(S_Y(\tau)/n)}=1.$$
--
--   The nonsingular-block assumption corrects the printed unqualified auxiliary limit: complementary singular mode projections satisfy the scattering constraint but make the rate identically zero. It is not imposed on the main qEPI. Independent moderation of this source correction remains pending.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 6, Section III C.3: limiting value of the entropy-power ratio

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

/-- PDF p.6, Section III C.3: limiting rate, with the necessary source correction.
Printed: the rate always tends to 1. Changed: require at least one nonsingular
block. Why: complementary singular mode projections obey the CCR sum but have
all weights and input noises zero, making the rate identically zero. The main
qEPI has no such restriction. Independent moderation of this correction is pending.
-/
theorem entropy_rate_limit {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (hEnergy : ∀ a, FiniteMeanEnergy (rho a).coefficients)
    (hActive : ∃ a, (C.block a).det ≠ 0)
    (clock : Fin K → ℝ → ℝ)
    (hclock : EntropyClocks C.block (fun a => (rho a).coefficients) clock) :
    Tendsto (fun tau => scatteringEntropyPowerRatio C (fun a => (rho a).coefficients)
      (fun a => clock a tau)) atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
