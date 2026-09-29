-- Prove2me | Theorems.Thm_StochasticOrders_MeanResidualLife_hazard_rate_order_imp_mrl_order
-- name    : StochasticOrders.MeanResidualLife.hazard_rate_order_imp_mrl_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:49.985977+00:00
-- url     : https://prove2.me/theorems/44b90365-fcd9-4343-8267-7e6b938683e5
-- title:
--   Theorem 2.A.1 — the hazard rate order implies the mean residual life order
-- statement:
--   If $X$ and $Y$ are two random variables such that $X \le_{hr} Y$, then $X \le_{mrl} Y$.
--
--   $$X \le_{hr} Y \implies X \le_{mrl} Y.$$
--
--   This is the one-directional link that motivates Theorem 2.A.2: the hazard rate order, being
--   strictly stronger in general, always implies the mean residual life order, and the goal
--   theorem identifies exactly the extra condition (monotonicity of $m/l$) under which the
--   implication reverses.
--
--   **Formalization Note** `X` and `Y` carry explicit `Integrable` hypotheses, formalizing the
--   book's standing "finite mean" assumption on every random variable it defines an mrl function
--   for (§2.A.1); without it, `mrl`'s Bochner integral could return its junk value `0`, making the
--   conclusion hold of a function that is not the book's actual mean residual life function.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 83, Theorem 2.A.1

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

/-- Theorem 2.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 83): if `X` and
`Y` are two random variables (with the chapter's standing finite-mean hypothesis, so that their
mrl functions are genuinely `E[X-t∣X>t]`/`E[Y-t∣Y>t]` and not the junk value the Bochner integral
returns for a non-integrable function) such that `X ≤hr Y`, then `X ≤mrl Y`. -/
theorem hazard_rate_order_imp_mrl_order {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν) (h : HazardRateOrder μ ν X Y) :
    MrlOrder μ ν X Y := by sorry

end StochasticOrders.MeanResidualLife
