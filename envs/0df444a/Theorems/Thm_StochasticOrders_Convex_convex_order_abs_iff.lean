-- Prove2me | Theorems.Thm_StochasticOrders_Convex_convex_order_abs_iff
-- name    : StochasticOrders.Convex.convex_order_abs_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:36.3308+00:00
-- url     : https://prove2.me/theorems/2abd4490-a81d-454f-9acf-7ce89975bc58
-- title:
--   Theorem 3.A.2 — the absolute-deviation characterization of the convex order
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be integrable random variables with
--   $E[X]=E[Y]$. Then
--
--   $$X \le_{cx} Y \iff E|X-a| \le E|Y-a| \quad \text{for all } a \in \mathbb{R}.$$
--
--   This is a fully self-contained alternative to Theorem 3.A.1's tail-integral form, needing no
--   external equation references: $X \le_{cx} Y$ holds exactly when $Y$'s mean absolute deviation
--   from every point $a$ dominates $X$'s. (The function $-E|X-\cdot|$ is called the *potential* of
--   $X$'s law, so this restates $X \le_{cx} Y$ as a pointwise comparison of the two potentials.)
--
--   **Formalization Note** `|X ω - a|` is Mathlib's absolute value on `ℝ`; no separate "potential"
--   definition is introduced since the theorem's content is fully captured by the raw inequality.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 111, Theorem 3.A.2

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

namespace StochasticOrders.Convex

open MeasureTheory

/-- Theorem 3.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 111): let `X`
and `Y` be two random variables with `E[X] = E[Y]`. Then `X ≤cx Y` iff `E|X - a| ≤ E|Y - a|` for
all `a ∈ ℝ`. -/
theorem convex_order_abs_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν) :
    ConvexOrder μ ν X Y ↔ ∀ a : ℝ, ∫ ω, |X ω - a| ∂μ ≤ ∫ ω, |Y ω - a| ∂ν := by sorry

end StochasticOrders.Convex
