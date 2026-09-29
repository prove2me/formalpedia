-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_apply_completely_monotone_deriv
-- name    : StochasticOrders.LaplaceTransform.laplace_order_apply_completely_monotone_deriv
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:26.129265+00:00
-- url     : https://prove2.me/theorems/8422d5bd-7d16-4110-8677-1ed7db556431
-- title:
--   Theorem 5.A.7(a) — closure under functions with a completely monotone derivative
-- statement:
--   If $X \le_{Lt} Y$ and $g$ is any positive function with a completely monotone derivative, then
--
--   $$g(X) \le_{Lt} g(Y).$$
--
--   This is the Laplace-transform-order analogue of "closure under increasing functions" for the
--   usual stochastic order: the class of transformations that preserve $\le_{Lt}$ is exactly the
--   positive functions whose derivative is completely monotone (which includes every $g(x) = x^p$,
--   $0 < p \le 1$, and every completely monotone $g$ itself), rather than all increasing functions.
--   The proof uses that if $\varphi$ is completely monotone and $g$ is positive with completely
--   monotone derivative, then $\varphi \circ g$ is completely monotone, together with Theorem
--   5.A.3.
--
--   **Formalization Note** "$g$ positive" is formalized as `0 < g x` for every `x ≥ 0` (the domain
--   on which $X$, $Y$ actually take values), not for every real `x`; "a completely monotone
--   derivative" is `CompletelyMonotone (deriv g)`, which already carries `g`'s own differentiability
--   since `CompletelyMonotone` requires `ContDiff ℝ ⊤ (deriv g)`.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 236, Theorem 5.A.7(a)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

/-- Theorem 5.A.7(a) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 236): if
`X ≤Lt Y` and `g` is any positive function with a completely monotone derivative, then
`g(X) ≤Lt g(Y)`. -/
theorem laplace_order_apply_completely_monotone_deriv {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (g : ℝ → ℝ) (hgmeas : Measurable g)
    (hgpos : ∀ x, 0 ≤ x → 0 < g x) (hgderiv : CompletelyMonotone (deriv g))
    (h : LaplaceOrder μ ν X Y) :
    LaplaceOrder μ ν (g ∘ X) (g ∘ Y) := by sorry

end StochasticOrders.LaplaceTransform
