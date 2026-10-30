-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_divergence_reciprocal_convex
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.divergence_reciprocal_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:23:48.1799+00:00
-- url     : https://prove2.me/theorems/524adf70-53c7-41f6-b3d6-f3b4be58a745
-- title:
--   Convexity in reciprocal Rényi order
-- statement:
--   Let $\rho,\sigma$ be finite-dimensional density matrices, and use the natural-log sandwiched divergence with $+\infty$ on support failure. Set $F(1)=0$ and, for $a>1$, $F(a)=(1-1/a)D_a(\rho\|\sigma)$. For $1\leq\alpha<\beta<\gamma$, let $\theta$ be uniquely specified by $1/\beta=(1-\theta)/\alpha+\theta/\gamma$. Then
--
--   $$F(\beta)\leq(1-\theta)F(\alpha)+\theta F(\gamma).$$
--
--   Equivalently, $G(x)=F(1/x)$ satisfies the explicit Jensen inequality
--
--   $$G((1-t)x+ty)\leq(1-t)G(x)+tG(y)\qquad(0<x,y\leq1,\ 0\leq t\leq1).$$
--
--   This is extended-real convexity in reciprocal order. The source’s order-one endpoint is completed by the scaled value zero before evaluating any divergence; this also specifies the endpoint on support failure.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 10, Theorem 8: convexity in reciprocal order

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- Beigi, arXiv:1306.5920v6, Theorem 8, PDF p.10: the displayed inequality
and its explicit reciprocal-order Jensen assertion. At a=1 the scaled value is zero,
as pinned in the plan, rather than a totalized value for D_1. -/
theorem divergence_reciprocal_convex {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ a b c : ℝ, 1 ≤ a → a < b → b < c →
      scaledDivergence b rho sigma ≤
        ((1 - interpolationWeight a b c : ℝ) : EReal) * scaledDivergence a rho sigma +
        ((interpolationWeight a b c : ℝ) : EReal) * scaledDivergence c rho sigma) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) 1, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      scaledDivergence (1 / ((1 - t) * x + t * y)) rho sigma ≤
        ((1 - t : ℝ) : EReal) * scaledDivergence (1 / x) rho sigma +
        ((t : ℝ) : EReal) * scaledDivergence (1 / y) rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
