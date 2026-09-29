-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_exists_isotropic_lift
-- name    : RobustMeanCov.Projection.exists_isotropic_lift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:45:41.593541+00:00
-- url     : https://prove2.me/theorems/11d66f4c-875c-47c1-8287-c18324f62df2
-- title:
--   Every $(0,1)$ law is the law of $y'\mathbf Z$ for some $\mathbf Z\sim(0,I_n)$, when $y'y=1$
-- statement:
--   Let $y\in\mathbb{R}^n$ with $y'y = 1$, and let $\zeta$ be a law in $\mathbb{M}_{(0,1)}$ (mean $0$, variance $1$). Then there is a law $Q\in\mathbb{M}^n_{(0,I_n)}$ (mean vector $0$, covariance matrix the identity) such that, if $\mathbf Z$ has law $Q$, the scalar $y'\mathbf Z$ has law $\zeta$:
--
--   $$
--   Q \circ (Z \mapsto y'Z)^{-1} = \zeta .
--   $$
--
--   This is the isotropic core of the general projection property: once the target law is standardized and the direction normalized, it remains to lift a univariate $(0,1)$ law to an $n$-variate $(0,I_n)$ law along a unit direction.
--
--   **Formalization Note** The paper constructs $\mathbf Z$ with $\mathbf z = y'\mathbf Z$ pathwise; since the theorem concerns distributions, the claim is stated about laws, as an equality of pushforward measures. The hypothesis $y'y=1$ forces $n\ge 1$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, pp. 109–110, Appendix, proof of Theorem 1: 'We first construct a random vector Z … ∼ (0, I_n) … such that z = y′Z' (p. 109) and 'This shows that the random vector Z … ∼ (0, I_n) satisfies z = y′Z (pathwise)' (p. 110)

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1 (Popescu 2007, pp. 109–110): for a unit vector `y` and a law
`z ∼ (0, 1)`, there is a random vector `Z ∼ (0, Iₙ)` with `y′Z` distributed as `z`. -/
theorem exists_isotropic_lift {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (hy : ⟪y, y⟫ = 1)
    (ζ : Measure ℝ) (hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1) :
    ∃ Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ),
      Q.map (fun Z => ⟪y, Z⟫) = ζ := by sorry

end RobustMeanCov.Projection
