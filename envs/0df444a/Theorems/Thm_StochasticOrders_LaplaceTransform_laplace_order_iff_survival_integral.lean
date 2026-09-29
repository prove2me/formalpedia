-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_iff_survival_integral
-- name    : StochasticOrders.LaplaceTransform.laplace_order_iff_survival_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:30.604251+00:00
-- url     : https://prove2.me/theorems/a0e2c516-dbd0-4d70-8333-f4162ba1df28
-- title:
--   Theorem 5.A.1 — the Laplace transform order via integrated survival functions
-- statement:
--   Let $X$ and $Y$ be two nonnegative random variables with survival functions $\bar F$ and $\bar
--   G$, respectively. Then
--
--   $$X \le_{Lt} Y \iff \int_0^\infty e^{-sx}\bar F(x)\,dx \le \int_0^\infty e^{-sx}\bar G(x)\,dx
--     \quad \text{for all } s > 0.$$
--
--   This is the book's principal alternative characterization of the Laplace transform order: it
--   restates the raw comparison of Laplace transforms $E[e^{-sX}]$ against $E[e^{-sY}]$ as a
--   comparison of the *integrated survival functions* weighted by $e^{-sx}$, via the identity
--   $\int_0^\infty e^{-sx}\bar F(x)\,dx = s^{-1}(1 - E[e^{-sX}])$. It is the natural goal for this
--   mission: the chapter's own defining equation (5.A.1) plus this identity is exactly how the book
--   proves it, and every later closure property in the chapter is phrased in terms of $\le_{Lt}$
--   itself, so this theorem is the bridge connecting the order's two standard faces.
--
--   **Formalization Note** $\bar F(x) = P\{X > x\}$ is formalized inline as `(μ {ω | x < X ω}).toReal`
--   (the `ENNReal`-valued measure of the tail set, converted to `ℝ`, well-defined and finite since
--   `μ` is a probability measure); the integral is taken over `Set.Ici (0 : ℝ)`, matching the book's
--   $\int_0^\infty$.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 234, Theorem 5.A.1

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

/-- Theorem 5.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 234): let `X` and
`Y` be two nonnegative random variables with survival functions `F` and `G`. Then `X ≤Lt Y` if, and
only if, `∫₀^∞ e^{-sx} F(x) dx ≤ ∫₀^∞ e^{-sx} G(x) dx` for all `s > 0`. -/
theorem laplace_order_iff_survival_integral {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) :
    LaplaceOrder μ ν X Y ↔
      ∀ s : ℝ, 0 < s →
        ∫ x in Set.Ici (0 : ℝ), Real.exp (-(s * x)) * (μ {ω | x < X ω}).toReal ≤
          ∫ x in Set.Ici (0 : ℝ), Real.exp (-(s * x)) * (ν {ω | x < Y ω}).toReal := by sorry

end StochasticOrders.LaplaceTransform
