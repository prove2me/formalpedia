-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_heat_entropy_lower_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.heat_entropy_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:13:38.639689+00:00
-- url     : https://prove2.me/theorems/52eedc61-90c2-4b5d-bf74-5e0492b476b9
-- title:
--   Section III C.1, Eq.(34): lower bound for noisy-state entropy
-- statement:
--   Let $n\ge1$, let $\rho$ be an arbitrary normalized full $n$-mode density, and let $\gamma$ be a real positive-definite noise matrix. There exists $t_1\ge1$, depending only on the fixed mode count and noise and uniform over all input densities, such that $t_1\gamma$ is a physical covariance, and for every $t\ge2t_1$ the covariance $(t-t_1)\gamma$ is physical and
--
--   $$S(H_\gamma(t)\rho)\ge S(\rho_{0,(t-t_1)\gamma}).$$
--
--   Here $\rho_{0,V}$ is the constructed centered Gaussian density with covariance $V$, and entropy retains $+\infty$. This exact Gaussian lower bound avoids an inequality containing an unspecified signed asymptotic remainder.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 5, Section III C.1, Eq.(34): lower bound for noisy-state entropy

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

/-- PDF p.5, Section III C.1, (34): exact Gaussian lower bound, valid even
for infinite-entropy input. t1 is constructed, not an assumed covariance bound.
Only t1*gamma and (t-t1)*gamma must be physical covariances. -/
theorem heat_entropy_lower_bound {n : ℕ} (hn : 0 < n)
    (gamma : Cov n) (hGamma : gamma.PosDef) :
    ∃ t1 : ℝ, 1 ≤ t1 ∧ PhysicalCovariance (t1 • gamma) ∧
      ∀ (rho : State (FockIndex n)) (t : ℝ), 2 * t1 ≤ t →
        PhysicalCovariance ((t - t1) • gamma) ∧
        extendedEntropyNats (gaussianCoefficient ((t - t1) • gamma) 0) ≤
          extendedEntropyNats (anisotropicHeat gamma t rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
