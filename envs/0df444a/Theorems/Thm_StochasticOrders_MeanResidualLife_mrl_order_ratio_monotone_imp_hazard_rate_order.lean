-- Prove2me | Theorems.Thm_StochasticOrders_MeanResidualLife_mrl_order_ratio_monotone_imp_hazard_rate_order
-- name    : StochasticOrders.MeanResidualLife.mrl_order_ratio_monotone_imp_hazard_rate_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:26:27.92331+00:00
-- url     : https://prove2.me/theorems/d93373e2-1db8-48af-8196-bd5e3a92957b
-- title:
--   Theorem 2.A.2 — mrl order plus monotone ratio implies the hazard rate order
-- statement:
--   Let $X$ and $Y$ be two random variables with mrl functions $m$ and $l$, respectively. Suppose
--   that $m(t)/l(t)$ increases in $t$ (over the region where $l(t) > 0$, where the ratio is
--   meaningful). Then, if $X \le_{mrl} Y$, then $X \le_{hr} Y$.
--
--   $$\left(\frac{m(t)}{l(t)} \text{ increasing}\right) \text{ and } X \le_{mrl} Y \implies X
--   \le_{hr} Y.$$
--
--   Combined with Theorem 2.A.1 (below), this gives an "iff" between $\le_{mrl}$ and $\le_{hr}$
--   under the monotone-ratio hypothesis: without that hypothesis, the book notes explicitly that
--   neither $\le_{st}$ nor $\le_{mrl}$ implies the other. The proof differentiates $m$ and $l$ and
--   compares the resulting hazard rate expressions $r(t) = m'(t)/m(t) + 1/m(t)$; that proof is not
--   formalized here.
--
--   **Formalization Note** "$m(t)/l(t)$ increases in $t$" is formalized as `MonotoneOn (fun t =>
--   mrl μ X t / mrl ν Y t) {t | 0 < mrl ν Y t}` — monotonicity of the genuine ratio, restricted to
--   where the denominator $l(t)$ is positive (where the ratio is not a division-by-zero junk
--   value), not two separate monotonicity hypotheses on $m$ and $l$ individually (a different,
--   unrelated condition per this chapter's own pitfall). `X` and `Y` carry explicit `Integrable`
--   hypotheses, formalizing the book's standing "finite mean" assumption on every random variable
--   it defines an mrl function for (§2.A.1): without it, the Bochner integral inside `mrl` returns
--   its junk value `0` for a non-integrable variable, which would let the hypotheses hold vacuously
--   of the book's actual mean residual life function.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 83, Theorem 2.A.2

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

/-- Theorem 2.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 83): let `X` and
`Y` be two random variables (with the chapter's standing finite-mean hypothesis, so their mrl
functions `m`, `l` are genuinely `E[X-t∣X>t]`/`E[Y-t∣Y>t]`) with mrl functions `m` and `l`. Suppose
`m(t)/l(t)` increases in `t` (over the region `l(t) > 0` where the ratio is meaningful). Then, if
`X ≤mrl Y`, `X ≤hr Y`. -/
theorem mrl_order_ratio_monotone_imp_hazard_rate_order {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (hratio : MonotoneOn (fun t => mrl μ X t / mrl ν Y t) {t : ℝ | 0 < mrl ν Y t})
    (h : MrlOrder μ ν X Y) :
    HazardRateOrder μ ν X Y := by sorry

end StochasticOrders.MeanResidualLife
