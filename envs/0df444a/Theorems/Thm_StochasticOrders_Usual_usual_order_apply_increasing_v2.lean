-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_apply_increasing_v2
-- name    : StochasticOrders.Usual.usual_order_apply_increasing_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:27.980288+00:00
-- url     : https://prove2.me/theorems/a5ad50ac-fb17-41de-822d-cf3ebe520c50
-- title:
--   Theorem 1.A.3(a) — closure of the usual stochastic order under increasing functions (corrected: probability spaces)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be real-valued random variables (measurable functions on probability spaces). If $X \le_{st} Y$ and $g : \mathbb{R} \to \mathbb{R}$ is any increasing function, then
--
--   $$g(X) \le_{st} g(Y).$$
--
--   This is the first and most immediate payoff of the order's definition: it is preserved under applying the same increasing transformation to both sides. (The bracketed decreasing case of Theorem 1.A.3(a) is a separate statement, `usual_order_apply_decreasing`.) The proof passes from the open tail events $\{X > a\}$ to the closed ones $\{X \ge a\}$ by continuity from above, which is where the probability (finite) measures are used.
--
--   **Formalization Note.** The retired version had bare measures $\mu$, $\nu$ and bare functions $X$, $Y$: for the infinite measure $\top$ the step from $\{X > a\}$ to $\{X \ge a\}$ fails, and it was refuted with a monotone step function $g$. The new statement makes the book's standing convention explicit: `[IsProbabilityMeasure μ]`, `[IsProbabilityMeasure ν]` (also needed for a constant $g$, where the conclusion reads $\mu(\Omega) \le \nu(\Omega')$), and `Measurable X`, `Measurable Y`. A monotone $g : \mathbb{R}\to\mathbb{R}$ is automatically Borel, so, exactly as in the book, no measurability of $g$ is assumed. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 6, Theorem 1.A.3(a)

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace StochasticOrders.Usual

open MeasureTheory

/-- Theorem 1.A.3(a) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 6): if
`X ≤st Y` and `g` is any increasing function, then `g(X) ≤st g(Y)`.

Corrected version (`_v2`) of `usual_order_apply_increasing`: the retired statement had bare
measures `μ`, `ν` and bare functions `X`, `Y`, and failed for the infinite measure `⊤` (the proof
passes from `{X > a}` to `{X ≥ a}` by continuity from above, and needs `μ univ = ν univ` for a
constant `g`). The book's standing convention — `X`, `Y` are random variables on probability
spaces — is now explicit: `[IsProbabilityMeasure μ]`, `[IsProbabilityMeasure ν]`, `Measurable X`,
`Measurable Y`. A monotone `g : ℝ → ℝ` is automatically Borel, so no measurability of `g` is
assumed, exactly as in the book. -/
theorem usual_order_apply_increasing_v2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (g : ℝ → ℝ) (hg : Monotone g) (h : UsualOrder μ ν X Y) :
    UsualOrder μ ν (g ∘ X) (g ∘ Y) := by sorry

end StochasticOrders.Usual
