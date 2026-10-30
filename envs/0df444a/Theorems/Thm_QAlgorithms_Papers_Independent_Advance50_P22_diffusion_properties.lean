-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_diffusion_properties
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.diffusion_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:07:27.320027+00:00
-- url     : https://prove2.me/theorems/9ca7fce9-d173-4fb6-b72f-552f703999b3
-- title:
--   Section III A, Eqs.(13)–(14): translation covariance and diffusion of moments
-- statement:
--   Let $n\ge1$, let $\rho$ be a normalized full $n$-mode density, and let the real noise matrix $\gamma$ be positive definite or zero. Let $H_\gamma(t)$ denote the Gaussian displacement-average heat flow for $t\ge0$, and let $D_x$ translate the quadrature means by $x\in\mathbb R^{2n}$. This flow preserves densities, is a semigroup, commutes with translations, and has characteristic action
--
--   $$\chi_{H_\gamma(t)\rho}(k)=e^{-t k^T\gamma k/4}\chi_\rho(k),\qquad H_\gamma(t)(D_x\rho D_x^\dagger)=D_xH_\gamma(t)(\rho)D_x^\dagger.$$
--
--   If the input has finite moments, so does the evolved state; its means are unchanged and its full anticommutator covariance is $\sigma(t)=\sigma(0)+t\gamma$. These identities specify the rigorous semigroup form of the diffusion equations.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 3, Section III A, Eqs.(13)–(14): translation covariance and diffusion of moments

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

/-- PDF p.3, Section III A, (13)--(14): translation covariance, the semigroup
law, and unchanged means with covariance increment t*gamma. The characteristic
multiplier fixes the scalar 1/4 without applying an unbounded generator to states.
The moment clause alone requires finite energy. -/
theorem diffusion_properties {n : ℕ} (hn : 0 < n) (rho : State (FockIndex n))
    (gamma : Cov n) (hGamma : gamma = 0 ∨ gamma.PosDef) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      anisotropicHeat gamma (s + t) rho.coefficients =
        anisotropicHeat gamma s (anisotropicHeat gamma t rho.coefficients)) ∧
    (∀ t : ℝ, 0 ≤ t → IsDensity (anisotropicHeat gamma t rho.coefficients) ∧
      (∀ x : InterleavedCoordinateVector n, anisotropicHeat gamma t (translateDensity x rho.coefficients) =
        translateDensity x (anisotropicHeat gamma t rho.coefficients)) ∧
      (∀ k : InterleavedCoordinateVector n, multimodeWeylTrace (anisotropicHeat gamma t rho.coefficients) k =
        (Real.exp (-t * (∑ i, ∑ j, k i * gamma i j * k j) / 4) : ℂ) *
          multimodeWeylTrace rho.coefficients k) ∧
      (FiniteMeanEnergy rho.coefficients →
        FiniteMeanEnergy (anisotropicHeat gamma t rho.coefficients) ∧
        firstMoments (anisotropicHeat gamma t rho.coefficients) = firstMoments rho.coefficients ∧
        quadratureCovariance (anisotropicHeat gamma t rho.coefficients) =
          quadratureCovariance rho.coefficients + t • gamma)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
