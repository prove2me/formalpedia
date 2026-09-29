-- Prove2me | Theorems.Thm_Rudin_ch05_deriv_sum_product
-- name    : Rudin.ch05_deriv_sum_product
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T04:15:00.441523+00:00
-- url     : https://prove2.me/theorems/9b20cdba-e564-4bb2-8c34-eb3e637d87eb
-- title:
--   Theorem 5.3(a,b) — the derivative of a sum and of a product
-- statement:
--   Let $f$ and $g$ be real functions of a real variable and let $x$ be a point at which both $f$ and $g$ are differentiable. Then the sum $f+g$ and the product $fg$ are differentiable at $x$, and their derivatives are
--
--   $$(f+g)'(x) = f'(x) + g'(x), \qquad (fg)'(x) = f'(x)g(x) + f(x)g'(x).$$
--
--   These are the first two parts of the elementary algebra of derivatives. Together with the quotient rule and the chain rule they reduce the differentiation of any expression built from differentiable functions to the derivatives of its constituents, and they are used silently throughout the rest of the chapter — for instance in forming the auxiliary function of the generalized mean value theorem and the remainder function of Taylor's theorem.
--
--   **Formalization Note** Differentiability is asserted explicitly alongside each derivative formula, because the derivative operator used here is a total function that returns $0$ at points where the function is not differentiable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 104, Theorem 5.3

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.3 (a), (b): if `f` and `g` are differentiable at `x`, then so are `f + g`
and `f * g`, and `(f + g)'(x) = f'(x) + g'(x)`, `(f g)'(x) = f'(x) g(x) + f(x) g'(x)`. -/
theorem ch05_deriv_sum_product (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun t => f t + g t) x ∧
      deriv (fun t => f t + g t) x = deriv f x + deriv g x ∧
    DifferentiableAt ℝ (fun t => f t * g t) x ∧
      deriv (fun t => f t * g t) x = deriv f x * g x + f x * deriv g x := by sorry

end Rudin
