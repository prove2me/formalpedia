-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_output_heat_compatibility
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.output_heat_compatibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:08:32.63099+00:00
-- url     : https://prove2.me/theorems/648c5611-1d84-41f1-9ab7-1f4a62f8564e
-- title:
--   Section III A, Eqs.(17)–(18): output evolution
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian scattering channel with real blocks $M_\alpha$, and let $\rho_\alpha$ be independent normalized full $n$-mode densities. Define the determinant weights $\lambda_\alpha$ and input noises $\gamma_\alpha$ as above, with zero noise for singular blocks. For arbitrary local times $t_\alpha\ge0$, set $t_Y=\sum_\alpha\lambda_\alpha t_\alpha$. Then
--
--   $$\Phi\!\left(\bigotimes_\alpha H_{\gamma_\alpha}(t_\alpha)\rho_\alpha\right)=H_I(t_Y)\Phi\!\left(\bigotimes_\alpha\rho_\alpha\right).$$
--
--   When the inputs have finite moments, the output covariance is $\sigma_Y(0)+t_YI$. The identity includes $t_Y=0$, making the output evolution well-defined even if all determinant weights vanish.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III A, Eqs.(17)–(18): output evolution

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

/-- PDF p.4, Section III A, (17)--(18): arbitrary local-time heat compatibility.
It includes t_Y=0; there is no division by t_Y and no derivative at zero speed. -/
theorem output_heat_compatibility {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (times : Fin K → ℝ) (htimes : ∀ a, 0 ≤ times a) :
    (C.channel (independentInput (evolvedInputs C.block
      (fun a => (rho a).coefficients) times)) =
    anisotropicHeat 1 (outputTime C.block times)
      (C.channel (independentInput (fun a => (rho a).coefficients)))) ∧
    ((∀ a, FiniteMeanEnergy (rho a).coefficients) →
      quadratureCovariance (C.channel (independentInput (evolvedInputs C.block
        (fun a => (rho a).coefficients) times))) =
      quadratureCovariance (C.channel (independentInput (fun a => (rho a).coefficients))) +
        outputTime C.block times • (1 : Cov n)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
