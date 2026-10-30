-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_heat_entropy_upper_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.heat_entropy_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:14:54.551973+00:00
-- url     : https://prove2.me/theorems/81286a9c-a33e-4879-8c4e-45eafc4ec3a2
-- title:
--   Section III C.2, Eq.(36): upper bound for noisy-state entropy
-- statement:
--   Let $n\ge1$, let $\rho$ be a normalized full $n$-mode density of finite mean photon number, and let $\gamma$ be real positive definite. Write $\sigma$ for the full anticommutator covariance of $\rho$. There exists $t_2>0$ with $\sigma\preceq t_2\gamma$ such that for all $t\ge0$,
--
--   $$S(H_\gamma(t)\rho)\le S(\rho_{0,(t_2+t)\gamma}).$$
--
--   Moreover there exist $C,T>0$, depending on the fixed input and noise, such that for all $t\ge T$ this Gaussian entropy is finite and
--
--   $$\left|S(\rho_{0,(t_2+t)\gamma})-n\ln\frac{et}{2}-\frac12\ln\det\gamma\right|\le\frac Ct.$$
--
--   This states both the constructed covariance comparison and the upper asymptotic bound.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 6, Section III C.2, Eq.(36): upper bound for noisy-state entropy

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

/-- PDF p.6, Section III C.2, (36): constructed comparison t2 and exact
Gaussian upper bound, with the real asymptotic remainder bounded by C/t.
Constants follow the fixed state and noise, before the varying time. -/
theorem heat_entropy_upper_bound {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients)
    (gamma : Cov n) (hGamma : gamma.PosDef) :
    ∃ t2 : ℝ, 0 < t2 ∧
      (t2 • gamma - quadratureCovariance rho.coefficients).PosSemidef ∧
      (∀ t : ℝ, 0 ≤ t →
        extendedEntropyNats (anisotropicHeat gamma t rho.coefficients) ≤
          extendedEntropyNats (gaussianCoefficient ((t2 + t) • gamma) 0)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
        extendedEntropyNats (gaussianCoefficient ((t2 + t) • gamma) 0) ≠ ⊤ ∧
        |(extendedEntropyNats (gaussianCoefficient ((t2 + t) • gamma) 0)).toReal -
          ((n : ℝ) * Real.log (Real.exp 1 * t / 2) + Real.log gamma.det / 2)| ≤ C / t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
