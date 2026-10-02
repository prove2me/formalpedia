-- Prove2me | Theorems.Thm_StochasticOrders_MultivariateVariability_convex_order_imp_mean_eq
-- name    : StochasticOrders.MultivariateVariability.convex_order_imp_mean_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:51.998853+00:00
-- url     : https://prove2.me/theorems/a636f939-003b-40da-90e1-84c610340385
-- title:
--   Eq. (7.A.5) — the multivariate convex order forces equal means
-- statement:
--   For any $i=1,\dots,n$, the coordinate projection $\varphi_i(x)=x_i$ and the function
--   $\psi_i(x)=-x_i$ are both convex. Therefore, from the definition of $\le_{cx}$ it follows
--   that
--
--   $$X \le_{cx} Y \implies E[X] = E[Y],$$
--
--   provided the expectations exist (componentwise equality of the two mean vectors in
--   $\mathbb{R}^n$). A cheap but useful corollary of `ConvexOrder`'s own defining quantifier,
--   applied to $\pm$ each coordinate projection.
--
--   **Formalization Note** The integrability of $X$ and $Y$ (i.e. that the mean vectors exist)
--   is carried as explicit hypotheses `Integrable X μ`, `Integrable Y ν`, matching the book's own
--   "provided the expectations exist" qualifier — not automatic, per this chapter's pitfall 4.
--   The conclusion `∫ X ∂μ = ∫ Y ∂ν` is Bochner-integral equality of two `Fin n → ℝ`-valued
--   vectors, i.e. componentwise equality.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 324, Eq. (7.A.5)

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

namespace StochasticOrders.MultivariateVariability

open MeasureTheory

/-- Eq. (7.A.5) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 324): for any
`i = 1, …, n`, the coordinate projection `φᵢ(x) = xᵢ` and its negation `ψᵢ(x) = −xᵢ` are both
convex, so `X ≤cx Y` implies `E[X] = E[Y]` (componentwise), provided the expectations exist. -/
theorem convex_order_imp_mean_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hord : ConvexOrder μ ν X Y) :
    ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν := by sorry

end StochasticOrders.MultivariateVariability
