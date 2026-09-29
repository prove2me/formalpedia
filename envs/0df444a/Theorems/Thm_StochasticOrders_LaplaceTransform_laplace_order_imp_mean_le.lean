-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_imp_mean_le
-- name    : StochasticOrders.LaplaceTransform.laplace_order_imp_mean_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:03.947989+00:00
-- url     : https://prove2.me/theorems/ceee38e7-2db1-4769-8559-29c2b13f4281
-- title:
--   Eq. (5.A.5) — the Laplace transform order implies ordered means
-- statement:
--   If $X \le_{Lt} Y$, then $E[X] \le E[Y]$, provided the expectations exist.
--
--   $$X \le_{Lt} Y \implies E[X] \le E[Y].$$
--
--   This is obtained by dividing the defining inequality by $s$ and letting $s \downarrow 0$; it is
--   the Laplace-transform-order analogue of the corresponding fact for the convex and increasing
--   convex orders, and the cheapest nontrivial consequence of the order to state as its own
--   milestone.
--
--   **Formalization Note** "Provided the expectations exist" becomes explicit `Integrable X μ` and
--   `Integrable Y ν` hypotheses, added rather than left implicit, per `CAPTAIN_BRIEF.md`'s rule on
--   explicit statements.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 234, Eq. (5.A.5)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

/-- Eq. (5.A.5) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 234): if `X ≤Lt Y`,
then `E[X] ≤ E[Y]`, provided the expectations exist. -/
theorem laplace_order_imp_mean_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXnn : ∀ ω, 0 ≤ X ω)
    (hYnn : ∀ ω, 0 ≤ Y ω) (hXint : Integrable X μ) (hYint : Integrable Y ν)
    (h : LaplaceOrder μ ν X Y) :
    ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂ν := by sorry

end StochasticOrders.LaplaceTransform
