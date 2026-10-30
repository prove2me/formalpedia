-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_scattering_covariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.scattering_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:06:50.673631+00:00
-- url     : https://prove2.me/theorems/af37142b-8e66-46cf-847c-7f2fdcd5a562
-- title:
--   Section II, Eq.(3) in the quantum setting: covariance transformation
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian linear scattering channel with blocks $M_\alpha$ satisfying the canonical commutation constraint, and let its independent normalized $n$-mode inputs have finite first and second quadrature moments. Use interleaved coordinates, $[Q_i,P_j]=i\delta_{ij}$, and the full centered anticommutator covariance, so the vacuum covariance is $I$. The output has finite moments, and
--
--   $$\sigma_Y=\sum_\alpha M_\alpha\sigma_\alpha M_\alpha^T.$$
--
--   This identifies the quantum covariance transformation with the classical linear-mixing rule without restricting the inputs to Gaussian states.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 2, Section II, Eq.(3) in the quantum setting: covariance transformation

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

/-- PDF p.2, Section II, (3),(8): quantum covariance transformation on the
finite-moment domain; output finite moments are part of the conclusion. -/
theorem scattering_covariance {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (hEnergy : ∀ a, FiniteMeanEnergy (rho a).coefficients) :
    FiniteMeanEnergy (C.channel (independentInput (fun a => (rho a).coefficients))) ∧
    quadratureCovariance (C.channel (independentInput (fun a => (rho a).coefficients))) =
      ∑ a, C.block a * quadratureCovariance (rho a).coefficients *
        (C.block a).transpose := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
