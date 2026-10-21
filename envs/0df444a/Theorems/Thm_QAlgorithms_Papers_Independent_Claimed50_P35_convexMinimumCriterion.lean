-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_convexMinimumCriterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.convexMinimumCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:43:08.164881+00:00
-- url     : https://prove2.me/theorems/76ca4589-030a-448c-9860-fc00118491dc
-- title:
--   Appendix A, Eq.(1.1): convex minimum criterion
-- statement:
--   Let $F$ be a real convex function on normalized density operators, and let $\rho_0$ be a density. Assume the finite right derivative $d_\sigma$ of $t\mapsto F((1-t)\rho_0+t\sigma)$ at zero exists for every density $\sigma$. Then
--
--   $$\rho_0\text{ minimizes }F\quad\Longleftrightarrow\quad d_\sigma\ge0\text{ for every density }\sigma.$$
--
--   The derivatives are taken along the feasible segment $0\le t\le1$ (an equivalent right germ is used). No differentiability on the ambient trace-class space or affinity of directional derivatives is assumed. This is the valid all-density criterion.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 11, Appendix A, Eq.(1.1): convex minimum criterion

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

/-- Appendix A, (1.1), p.11: all-density minimum criterion, with finite
right derivatives. No pure-direction reduction or derivative affinity is assumed. -/
theorem convexMinimumCriterion {I : Type} [Nonempty I]
    (F : Matrix I I ℂ → ℝ) (hconvex : ConvexOn ℝ {X | IsDensity X} F)
    (rho : State I) (d : State I → ℝ)
    (hd : ∀ sigma, HasDerivWithinAt
      (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t))
      (d sigma) (Set.Ici 0) 0) :
    (∀ sigma : State I, F rho.coefficients ≤ F sigma.coefficients) ↔
      ∀ sigma : State I, 0 ≤ d sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
