-- Prove2me | Theorems.Thm_StochasticOrders_Usual_hazard_rate_order_imp_usual_order_v2
-- name    : StochasticOrders.Usual.hazard_rate_order_imp_usual_order_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:41.472296+00:00
-- url     : https://prove2.me/theorems/4c4da190-2121-46fc-afdb-2fddc2209899
-- title:
--   Theorem 1.B.1 — the hazard rate order implies the usual stochastic order (corrected: probability spaces)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables (measurable functions on probability spaces). If $X \le_{hr} Y$, then $X \le_{st} Y$:
--
--   $$X \le_{hr} Y \implies X \le_{st} Y.$$
--
--   Here $X \le_{hr} Y$ is the general form (1.B.4) of the hazard rate order, $\bar F(y)\,\bar G(x) \le \bar F(x)\,\bar G(y)$ for all $x \le y$, with $\bar F$, $\bar G$ the survival functions of $X$, $Y$. This is the first link in the chain $\le_{lr} \implies \le_{hr} \implies \le_{st}$; the proof lets $x \to -\infty$ in the cross-product inequality and uses $\bar F(x), \bar G(x) \to 1$, which is where the probability measures enter.
--
--   **Formalization Note.** The retired version had bare measures $\mu$, $\nu$: with $\nu = 0$ the hazard-rate inequality is $0 \le 0$ while the usual order fails, and it was refuted. The new statement makes the book's standing convention explicit: `[IsProbabilityMeasure μ]`, `[IsProbabilityMeasure ν]`, `Measurable X`, `Measurable Y`. The imported `HazardRateOrder` is the book's (1.B.4) verbatim, in `ℝ≥0∞` arithmetic, which is exact for probabilities. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 18, Theorem 1.B.1

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_StochasticOrders_Usual_HazardRateOrder

namespace StochasticOrders.Usual

open MeasureTheory

/-- Theorem 1.B.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 18): if `X` and
`Y` are two random variables such that `X ≤hr Y`, then `X ≤st Y`.

Corrected version (`_v2`) of `hazard_rate_order_imp_usual_order`: the retired statement had bare
measures `μ`, `ν`, so `ν = 0` made the hazard-rate inequality `0 ≤ 0` while the usual order
failed (the book's proof lets `x → -∞` and uses `F̄(x), Ḡ(x) → 1`). The book's standing
convention — `X`, `Y` are random variables on probability spaces — is now explicit:
`[IsProbabilityMeasure μ]`, `[IsProbabilityMeasure ν]`, `Measurable X`, `Measurable Y`. -/
theorem hazard_rate_order_imp_usual_order_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h : HazardRateOrder μ ν X Y) :
    UsualOrder μ ν X Y := by sorry

end StochasticOrders.Usual
