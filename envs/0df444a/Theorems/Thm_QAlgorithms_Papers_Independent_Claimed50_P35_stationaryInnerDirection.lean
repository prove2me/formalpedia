-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_stationaryInnerDirection
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.stationaryInnerDirection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:43:28.169288+00:00
-- url     : https://prove2.me/theorems/116f4349-99f9-4b72-8a65-8e50fee82e36
-- title:
--   Appendix A, Eq.(1.2): stationary inner direction
-- statement:
--   Let $F$ be real and convex on density operators and let $\rho_0$ be a global minimizer. Let $\sigma$ be a density such that $(1-t)\rho_0+t\sigma$ remains a density for all sufficiently small positive and negative $t$. If the two-sided derivative along this line exists at zero, then
--
--   $$\left.\frac{d}{dt}F((1-t)\rho_0+t\sigma)\right|_{t=0}=0.$$
--
--   A stationary single direction is not asserted to imply a global minimum. The two-sided existence condition is essential for this inner-direction formulation.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 11, Appendix A, Eq.(1.2): stationary inner direction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- Appendix A, (1.2), p.11: an inner direction at a global minimum has
zero existing TWO-SIDED derivative. A single stationary line is not sufficient
for a global minimum. -/
theorem stationaryInnerDirection {I : Type} [Nonempty I]
    (F : Matrix I I ℂ → ℝ) (hconvex : ConvexOn ℝ {X | IsDensity X} F)
    (rho sigma : State I)
    (hmin : ∀ tau : State I, F rho.coefficients ≤ F tau.coefficients)
    (hinner : ∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Set.Ioo (-eta) eta,
      IsDensity (densityLine rho.coefficients sigma.coefficients t))
    (d : ℝ) (hd : HasDerivAt
      (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t)) d 0) :
    d = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
