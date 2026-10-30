-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_heat_entropy_power_asymptotics
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.heat_entropy_power_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:15:38.714133+00:00
-- url     : https://prove2.me/theorems/68d1d1ba-5d43-4bdc-8ecf-0b3d61c05525
-- title:
--   Section III C.3, Eq.(37): anisotropic heat entropy-power asymptotics
-- statement:
--   Let $n\ge1$, let $\rho$ be a normalized full $n$-mode density with finite mean photon number, and let $\gamma$ be a real positive-definite noise matrix. There exist $C,T>0$, depending on the fixed density and noise, such that for every $t\ge T$ the entropy is finite and
--
--   $$\left|\exp\!\left(\frac{S(H_\gamma(t)\rho)}n\right)-(\det\gamma)^{1/(2n)}\frac{et}{2}\right|\le C.$$
--
--   This is the anisotropic entropy-power expansion with an $O(1)$ remainder; no uniform bound over all input states is asserted.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 6, Section III C.3, Eq.(37): anisotropic heat entropy-power asymptotics

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

/-- PDF p.6, Section III C.3, (37): e*t, not exp(t), with O(1) allowed to
depend on the fixed density and positive-definite anisotropic noise. -/
theorem heat_entropy_power_asymptotics {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients)
    (gamma : Cov n) (hGamma : gamma.PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
      extendedEntropyNats (anisotropicHeat gamma t rho.coefficients) ≠ ⊤ ∧
      |Real.exp ((extendedEntropyNats (anisotropicHeat gamma t rho.coefficients)).toReal /
        (n : ℝ)) - gamma.det ^ (1 / (2 * (n : ℝ))) * Real.exp 1 * t / 2| ≤ C := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
