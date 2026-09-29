-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_iff_completely_monotone
-- name    : StochasticOrders.LaplaceTransform.laplace_order_iff_completely_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:56.317156+00:00
-- url     : https://prove2.me/theorems/cc33ad56-80c6-4fff-9157-10dbd87449d3
-- title:
--   Theorem 5.A.3 — characterization via completely monotone functions
-- statement:
--   Let $X$ and $Y$ be two nonnegative random variables. Then $X \le_{Lt} Y$ if, and only if,
--
--   $$E[\varphi(X)] \ge E[\varphi(Y)]$$
--
--   for all completely monotone functions $\varphi$, provided the expectations exist.
--
--   This is the order's "function class" characterization in the same style as the usual and
--   convex orders: instead of testing against the single family $\varphi_s(x) = e^{-sx}$, it is
--   equivalent to testing against the whole class of completely monotone functions, of which each
--   $\varphi_s$ is one member. The forward direction ($\Leftarrow$, taking $\varphi = \varphi_s$)
--   is immediate from the definition; the reverse direction uses that every completely monotone
--   $\varphi$ is a mixture $\int_0^\infty e^{-xu}\,\mu(du)$ of the $\varphi_s$'s.
--
--   **Formalization Note** The universal quantifier is over the *exact* function class the book
--   names — all completely monotone $\varphi : \mathbb{R} \to \mathbb{R}$ — with per-$\varphi$
--   integrability hypotheses `Integrable (φ ∘ X) μ` and `Integrable (φ ∘ Y) ν` standing in for
--   "provided the expectations exist", not a fixed or narrowed subclass.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 235, Theorem 5.A.3

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

/-- Theorem 5.A.3 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 235): let `X` and
`Y` be two nonnegative random variables. Then `X ≤Lt Y` if, and only if, `E[φ(X)] ≥ E[φ(Y)]` for
all completely monotone functions `φ`, provided the expectations exist. -/
theorem laplace_order_iff_completely_monotone {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) :
    LaplaceOrder μ ν X Y ↔
      ∀ φ : ℝ → ℝ, CompletelyMonotone φ → Integrable (φ ∘ X) μ → Integrable (φ ∘ Y) ν →
        ∫ ω, φ (Y ω) ∂ν ≤ ∫ ω, φ (X ω) ∂μ := by sorry

end StochasticOrders.LaplaceTransform
