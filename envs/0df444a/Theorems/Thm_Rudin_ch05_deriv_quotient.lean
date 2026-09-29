-- Prove2me | Theorems.Thm_Rudin_ch05_deriv_quotient
-- name    : Rudin.ch05_deriv_quotient
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T04:14:59.340845+00:00
-- url     : https://prove2.me/theorems/6e0d8360-0a41-482b-9fe5-2aa068bcb375
-- title:
--   Theorem 5.3(c) — the derivative of a quotient
-- statement:
--   Let $f$ and $g$ be real functions of a real variable, differentiable at a point $x$, and suppose $g(x) \ne 0$. Then the quotient $f/g$ is differentiable at $x$ and
--
--   $$\left(\frac{f}{g}\right)'(x) = \frac{g(x)f'(x) - g'(x)f(x)}{g(x)^2}.$$
--
--   This is part (c) of Rudin's Theorem 5.3. The hypothesis $g(x) \ne 0$ is what makes the quotient defined near $x$: since $g$ is differentiable at $x$ it is continuous there, so $g$ is nonzero on a whole neighbourhood of $x$ and the difference quotient of $f/g$ makes sense. The rule is the standard tool for differentiating rational expressions and is the form in which the derivative of $f/g$ enters L'Hospital's rule.
--
--   **Formalization Note** Differentiability is asserted explicitly alongside the derivative formula, because the derivative operator used here is a total function that returns $0$ at points where the function is not differentiable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 104, Theorem 5.3

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.3 (c): if `f` and `g` are differentiable at `x` and `g x ≠ 0`, then `f / g`
is differentiable at `x` and `(f / g)'(x) = (g(x) f'(x) - g'(x) f(x)) / g(x)^2`. -/
theorem ch05_deriv_quotient (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hgx : g x ≠ 0) :
    DifferentiableAt ℝ (fun t => f t / g t) x ∧
      deriv (fun t => f t / g t) x = (g x * deriv f x - deriv g x * f x) / (g x) ^ 2 := by sorry

end Rudin
