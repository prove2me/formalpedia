-- Prove2me | Theorems.Thm_StochasticOrders_Convex_convex_order_tail_integral_iff
-- name    : StochasticOrders.Convex.convex_order_tail_integral_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:49.721692+00:00
-- url     : https://prove2.me/theorems/d950e091-1431-480e-992f-14b8d60319ae
-- title:
--   Theorem 3.A.1 — tail-integral characterizations of the convex order
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be integrable random variables with
--   $E[X]=E[Y]$. Then
--
--   $$X \le_{cx} Y \iff \int_x^\infty \bar F(u)\,du \le \int_x^\infty \bar G(u)\,du \ \text{ for all } x,$$
--   $$X \le_{cx} Y \iff \int_{-\infty}^x F(u)\,du \le \int_{-\infty}^x G(u)\,du \ \text{ for all } x,$$
--
--   where $\bar F,\bar G$ are the survival functions and $F,G$ the distribution functions of $X,Y$.
--   These integral forms are what the book's own proof of Theorem 3.A.4 works with directly (via
--   $E[(X-a)^+]\le E[(Y-a)^+]$, integrated by parts), and are the natural stepping stone from the
--   convex order's defining "for every convex $\varphi$" quantifier to a two-family, pointwise
--   characterization.
--
--   **Formalization Note** Both equivalences share the equal-means and integrability hypotheses,
--   stated once as the theorem's context, matching the book's own "Let $X$ and $Y$ … such that
--   $E[X]=E[Y]$. Then (a) … (b) …" structure; the conjunction of the two `iff`s is drafted as a
--   single Lean theorem rather than two, since they share every hypothesis and the book states
--   them as the two parts of one theorem.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 110, Theorem 3.A.1

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

namespace StochasticOrders.Convex

open MeasureTheory

/-- Theorem 3.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 110): let `X`
and `Y` be two random variables with `E[X] = E[Y]`. Then (a) `X ≤cx Y` iff (3.A.7),
`∫_x^∞ F̄(u) du ≤ ∫_x^∞ Ḡ(u) du` for all `x`; and (b) `X ≤cx Y` iff (3.A.8),
`∫_{-∞}^x F(u) du ≤ ∫_{-∞}^x G(u) du` for all `x`. -/
theorem convex_order_tail_integral_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν) :
    (ConvexOrder μ ν X Y ↔
      ∀ x : ℝ, ∫ u in Set.Ici x, tailProb μ X u ≤ ∫ u in Set.Ici x, tailProb ν Y u) ∧
    (ConvexOrder μ ν X Y ↔
      ∀ x : ℝ, ∫ u in Set.Iic x, cdf μ X u ≤ ∫ u in Set.Iic x, cdf ν Y u) := by sorry

end StochasticOrders.Convex
