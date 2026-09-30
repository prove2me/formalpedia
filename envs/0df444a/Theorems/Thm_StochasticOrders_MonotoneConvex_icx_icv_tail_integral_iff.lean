-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icx_icv_tail_integral_iff
-- name    : StochasticOrders.MonotoneConvex.icx_icv_tail_integral_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:50.469201+00:00
-- url     : https://prove2.me/theorems/f17cd646-de95-4911-b9af-1b1d044a4869
-- title:
--   Theorem 4.A.2 — tail-integral characterizations of the increasing convex/concave orders
-- statement:
--   Let $X$ and $Y$ be two integrable random variables with survival functions $\bar F,\bar G$
--   and distribution functions $F,G$. Then
--
--   $$X \le_{icx} Y \iff \int_x^\infty \bar F(u)\,du \le \int_x^\infty \bar G(u)\,du
--     \ \text{ for all } x,$$
--   $$X \le_{icv} Y \iff \int_{-\infty}^x F(u)\,du \ge \int_{-\infty}^x G(u)\,du
--     \ \text{ for all } x.$$
--
--   The book derives these from the fact that every increasing convex [concave] function is a
--   limit of positive linear combinations of the functions $\varphi_a(x)=(x-a)^+$ [$\zeta_a(x) =
--   (x-a)^-$], whose expectations $E[(X-a)^+]$, $E[(X-a)^-]$ rewrite, by integration by parts, as
--   exactly these tail integrals.
--
--   **Formalization Note** Both equivalences share the integrability hypothesis on `X`, `Y`,
--   stated once as the theorem's context, matching the book's own "provided the integrals exist"
--   qualifier attached to (4.A.5)/(4.A.7); unlike Chunk 03's analogous Theorem 3.A.1 for the plain
--   convex order, no equal-means hypothesis is added, since the book states Theorem 4.A.2 without
--   one (the increasing convex/concave orders do not require equal means, only the one-directional
--   $E[X]\le E[Y]$ from (4.A.2)/(4.A.3)). The two `iff`s are drafted as a single Lean theorem
--   (conjunction, not `Or`) since they share every hypothesis and the book states them as the two
--   bracketed cases of one theorem.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 183, Theorem 4.A.2

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

/-- Theorem 4.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 183): let `X` and
`Y` be two integrable random variables. Then `X ≤icx Y` iff (4.A.5),
`∫_x^∞ F̄(u) du ≤ ∫_x^∞ Ḡ(u) du` for all `x`; and `X ≤icv Y` iff (4.A.7),
`∫_{-∞}^x F(u) du ≥ ∫_{-∞}^x G(u) du` for all `x`. -/
theorem icx_icv_tail_integral_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν) :
    (IcxOrder μ ν X Y ↔
      ∀ x : ℝ, tailUpperIntegral μ X x ≤ tailUpperIntegral ν Y x) ∧
    (IcvOrder μ ν X Y ↔
      ∀ x : ℝ, tailLowerIntegral ν Y x ≤ tailLowerIntegral μ X x) := by sorry

end StochasticOrders.MonotoneConvex
