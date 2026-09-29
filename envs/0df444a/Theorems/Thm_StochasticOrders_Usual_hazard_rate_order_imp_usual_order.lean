-- Prove2me | Theorems.Thm_StochasticOrders_Usual_hazard_rate_order_imp_usual_order
-- name    : StochasticOrders.Usual.hazard_rate_order_imp_usual_order
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:33:02.80737+00:00
-- url     : https://prove2.me/theorems/2f8ec3a3-ca5b-49ee-a758-825c085a4f82
-- title:
--   Theorem 1.B.1 — the hazard rate order implies the usual stochastic order
-- statement:
--   If $X$ and $Y$ are two random variables such that $X \le_{hr} Y$, then $X \le_{st} Y$.
--
--   $$X \le_{hr} Y \implies X \le_{st} Y.$$
--
--   This is the first link in the book's implication chain likelihood-ratio $\implies$ hazard-rate
--   $\implies$ usual ($\le_{lr} \implies \le_{hr} \implies \le_{st}$), obtained by taking $x \to
--   -\infty$ in the hazard rate order's defining cross-product inequality and recovering the usual
--   order's survival-function inequality. It is the single most citable fact about the usual
--   stochastic order for the rest of the series: every later chapter's own order for which a
--   hazard-rate-type or likelihood-ratio-type analogue exists implies $\le_{st}$ through the same
--   argument shape.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 18, Theorem 1.B.1

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_StochasticOrders_Usual_HazardRateOrder

namespace StochasticOrders.Usual

open MeasureTheory

/-- Theorem 1.B.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 18): if `X` and
`Y` are two random variables such that `X ≤hr Y`, then `X ≤st Y`. -/
theorem hazard_rate_order_imp_usual_order {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (h : HazardRateOrder μ ν X Y) :
    UsualOrder μ ν X Y := by sorry

end StochasticOrders.Usual
