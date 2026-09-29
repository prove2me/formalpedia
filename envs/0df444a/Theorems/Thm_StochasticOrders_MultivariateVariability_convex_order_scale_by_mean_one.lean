-- Prove2me | Theorems.Thm_StochasticOrders_MultivariateVariability_convex_order_scale_by_mean_one
-- name    : StochasticOrders.MultivariateVariability.convex_order_scale_by_mean_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:09.126176+00:00
-- url     : https://prove2.me/theorems/64790fe0-df5a-46a9-90f9-94fb98e84b57
-- title:
--   Theorem 7.A.9 — scaling a random vector by an independent mean-one factor
-- statement:
--   Let the random vector $X$ and the nonnegative random variable $U$ be independent. If
--   $E[U] = 1$, then
--
--   $$X \le_{cx} U X.$$
--
--   A simple, self-contained application: multiplying $X$ by an independent, mean-one random
--   scale factor always makes it larger in the convex (variability) order.
--
--   **Formalization Note** $U\cdot X$ is drafted as scalar multiplication `U ω • X ω` on the
--   module `Fin n → ℝ` over `ℝ`. Independence is `ProbabilityTheory.IndepFun`; nonnegativity of
--   `U` is the a.e. inequality `0 ≤ᵐ[μ] U`; both `X` and `U X` live on the same space `(Ω, μ)`,
--   matching the book's single-space statement (no separate coupling space is needed here, unlike
--   the goal and Theorem 7.A.2).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 328, Theorem 7.A.9

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

namespace StochasticOrders.MultivariateVariability

open MeasureTheory ProbabilityTheory

/-- Theorem 7.A.9 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 328): let the
random vector `X` and the nonnegative random variable `U` be independent. If `E[U] = 1`, then
`X ≤cx U·X`. -/
theorem convex_order_scale_by_mean_one {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin n → ℝ) (U : Ω → ℝ)
    (hX : Measurable X) (hU : Measurable U) (hIndep : IndepFun X U μ)
    (hUnn : 0 ≤ᵐ[μ] U) (hUmean : ∫ ω, U ω ∂μ = 1) :
    ConvexOrder μ μ X (fun ω => U ω • X ω) := by sorry

end StochasticOrders.MultivariateVariability
