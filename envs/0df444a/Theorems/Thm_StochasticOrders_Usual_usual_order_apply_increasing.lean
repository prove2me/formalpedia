-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_apply_increasing
-- name    : StochasticOrders.Usual.usual_order_apply_increasing
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:31:48.846988+00:00
-- url     : https://prove2.me/theorems/1d0ae100-d059-4782-bf62-834d6a54b356
-- title:
--   Theorem 1.A.3(a) — closure under monotone functions
-- statement:
--   If $X \le_{st} Y$ and $g : \mathbb{R} \to \mathbb{R}$ is any increasing function, then
--   $g(X) \le_{st} g(Y)$; if $g$ is any decreasing function, then $g(X) \ge_{st} g(Y)$, i.e.
--   $g(Y) \le_{st} g(X)$.
--
--   $$X \le_{st} Y,\ g \text{ increasing} \implies g(X) \le_{st} g(Y).$$
--
--   This is the first and most immediate payoff of the order's definition: it is preserved (or
--   reversed) under applying the same monotone transformation to both sides. It underlies many
--   later results, including the multivariate generalizations in Chapter 6.
--
--   **Formalization Note** Two theorems are drafted, one per monotonicity direction, matching the
--   book's bracketed "increasing [decreasing]" phrasing: `usual_order_apply_increasing` (`Monotone
--   g`) and `usual_order_apply_decreasing` (`Antitone g`, stated with the order reversed as
--   `UsualOrder ν μ (g ∘ Y) (g ∘ X)`).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 6, Theorem 1.A.3(a)

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace StochasticOrders.Usual

open MeasureTheory

/-- Theorem 1.A.3(a) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 6): if
`X ≤st Y` and `g` is any increasing function, then `g(X) ≤st g(Y)`. -/
theorem usual_order_apply_increasing {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (g : ℝ → ℝ) (hg : Monotone g)
    (h : UsualOrder μ ν X Y) :
    UsualOrder μ ν (g ∘ X) (g ∘ Y) := by sorry

end StochasticOrders.Usual
