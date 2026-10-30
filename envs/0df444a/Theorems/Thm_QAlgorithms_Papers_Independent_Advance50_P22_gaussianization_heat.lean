-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_gaussianization_heat
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.gaussianization_heat
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:14:22.62395+00:00
-- url     : https://prove2.me/theorems/7abbaa2d-676c-47a9-ae16-535fcbc57a48
-- title:
--   Section III C.2, Eq.(35): Gaussianization commutes with the heat flow
-- statement:
--   Let $n\ge1$, let $\rho$ be a normalized full $n$-mode density with finite mean photon number, and let $\rho_G$ be the constructed Gaussian density having its first and second moments. For real positive-definite or zero $\gamma$ and every $t\ge0$,
--
--   $$(H_\gamma(t)\rho)_G=H_\gamma(t)\rho_G,\qquad S(H_\gamma(t)\rho)\le S((H_\gamma(t)\rho)_G).$$
--
--   The equality implies that the Gaussian entropy on the right also equals $S(H_\gamma(t)\rho_G)$. This is the commutation and entropy comparison used in Eq. (35), with Gaussianization computed from the input rather than freely chosen.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 5, Section III C.2, Eq.(35): Gaussianization commutes with the heat flow

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

/-- PDF pp.5--6, Section III C.2, (35): Gaussianization is the constructed
moment-matched Gaussian, commutes with heat, and bounds its entropy above. -/
theorem gaussianization_heat {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients)
    (gamma : Cov n) (hGamma : gamma = 0 ∨ gamma.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    gaussification (anisotropicHeat gamma t rho.coefficients) =
      anisotropicHeat gamma t (gaussification rho.coefficients) ∧
    extendedEntropyNats (anisotropicHeat gamma t rho.coefficients) ≤
      extendedEntropyNats (gaussification (anisotropicHeat gamma t rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
