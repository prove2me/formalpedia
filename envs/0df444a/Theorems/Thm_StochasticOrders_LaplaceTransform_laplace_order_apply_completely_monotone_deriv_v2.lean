-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_apply_completely_monotone_deriv_v2
-- name    : StochasticOrders.LaplaceTransform.laplace_order_apply_completely_monotone_deriv_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:23.451024+00:00
-- url     : https://prove2.me/theorems/37bd5cd0-98f7-46fc-83a5-2f5700c7dcef
-- title:
--   Theorem 5.A.7(a) — closure of the Laplace transform order under positive functions with a completely monotone derivative (corrected)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be nonnegative random variables (measurable functions on probability spaces, the standing convention of §5.A). If $X \le_{Lt} Y$ and $g$ is any positive function on $[0,\infty)$ with a completely monotone derivative — $g$ continuous on $[0,\infty)$, differentiable on $(0,\infty)$ with $g'$ completely monotone there — then
--
--   $$g(X) \le_{Lt} g(Y).$$
--
--   This is the Laplace-transform-order analogue of closure under increasing functions: the transformations preserving $\le_{Lt}$ are the positive functions whose derivative is completely monotone (the Bernstein functions, e.g. $g(x) = x^p$ for $0 < p \le 1$, or any positive completely monotone $g$ itself). The proof uses that $\varphi \circ g$ is completely monotone whenever $\varphi$ is and $g$ has a completely monotone derivative, together with the characterization of $\le_{Lt}$ by completely monotone test functions (Theorem 5.A.3).
--
--   **Formalization Note.** The retired version constrained only the function `deriv g`, which Mathlib sets to the junk value $0$ wherever $g$ is not differentiable, so a decreasing step function qualified and the statement was refuted. The new statement says what "$g$ has a completely monotone derivative" means: $g$ is differentiable on $(0,\infty)$ (`DifferentiableOn ℝ g (Set.Ioi 0)`, so `deriv g` is the honest derivative there) and `deriv g` is completely monotone in the corrected sense (`CompletelyMonotone_v2`: $C^\infty$ on $(0,\infty)$ with the sign conditions for $x>0$; the retired definition demanded smoothness on all of $\mathbb{R}$, which excluded the book's own examples such as $x^p$). Since the book's $g$ is a function on the half-line $[0,\infty)$ where $X$, $Y$ take their values, it is continuous there (`ContinuousOn g (Set.Ici 0)`; continuity at $0$ from the right is exactly what the theorem needs when $X$ or $Y$ has an atom at $0$) and positive there (`0 < g x` for $x \ge 0$, the literal reading of "positive"); values of $g$ on $(-\infty,0)$ are irrelevant. Measurability of $g\circ X$, $g \circ Y$ follows from these hypotheses, so the retired `Measurable g` is not assumed. Nonnegativity of $X$, $Y$ is pointwise. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 236, Theorem 5.A.7(a)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone_v2

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

/-- Theorem 5.A.7(a) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 236): if
`X ≤Lt Y` (nonnegative random variables, the standing convention of §5.A) and `g` is any positive
function with a completely monotone derivative, then `g(X) ≤Lt g(Y)`.

Corrected version (`_v2`) of `laplace_order_apply_completely_monotone_deriv`: the retired
statement constrained only the function `deriv g`, which is the junk value `0` wherever `g` is not
differentiable, so a decreasing step function qualified. "`g` has a completely monotone
derivative" now says what the book means: `g` is differentiable on `(0, ∞)` and `deriv g` is
completely monotone there (`CompletelyMonotone` in its corrected `(0, ∞)`-based form, which no
longer demands smoothness of `g` on `(-∞, 0]`); `g` is a function on the half-line `[0, ∞)` where
`X`, `Y` live, hence continuous there (continuity at `0` from the right is what the theorem needs
when `X` or `Y` has an atom at `0`) and positive there. Measurability of `g ∘ X`, `g ∘ Y` follows
from these hypotheses, so none is assumed. -/
theorem laplace_order_apply_completely_monotone_deriv_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (g : ℝ → ℝ)
    (hgcont : ContinuousOn g (Set.Ici 0)) (hgdiff : DifferentiableOn ℝ g (Set.Ioi 0))
    (hgpos : ∀ x, 0 ≤ x → 0 < g x) (hgderiv : CompletelyMonotone (deriv g))
    (h : LaplaceOrder μ ν X Y) :
    LaplaceOrder μ ν (g ∘ X) (g ∘ Y) := by sorry

end StochasticOrders.LaplaceTransform
