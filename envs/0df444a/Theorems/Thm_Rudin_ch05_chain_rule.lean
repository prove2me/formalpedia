-- Prove2me | Theorems.Thm_Rudin_ch05_chain_rule
-- name    : Rudin.ch05_chain_rule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T04:14:59.249695+00:00
-- url     : https://prove2.me/theorems/cd8743a4-e408-4548-98d3-08aedec92714
-- title:
--   Theorem 5.5 — the chain rule
-- statement:
--   Let $f$ be a real function differentiable at a point $x$, and let $g$ be a real function differentiable at the point $f(x)$. Then the composite $h(t) = g(f(t))$ is differentiable at $x$ and
--
--   $$h'(x) = g'(f(x))\, f'(x).$$
--
--   This is the chain rule. It is the rule that makes differentiation compatible with substitution, and in the chapter it is used to differentiate the compositions that arise in changes of variable and in the vector-valued theory at the end of the chapter.
--
--   **Formalization Note** Rudin states the theorem for $f$ continuous on $[a,b]$ and $g$ defined on an interval containing the range of $f$; here both functions are defined on all of $\mathbb{R}$, so those domain hypotheses are automatic and only the two differentiability hypotheses remain. Differentiability of the composite is asserted explicitly alongside the derivative formula, because the derivative operator used here is a total function that returns $0$ at points where the function is not differentiable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, pp. 105-106, Theorem 5.5

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.5 (chain rule): if `f` is differentiable at `x` and `g` is differentiable
at `f x`, then `t ↦ g (f t)` is differentiable at `x` with derivative `g'(f x) * f'(x)`. -/
theorem ch05_chain_rule (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    DifferentiableAt ℝ (fun t => g (f t)) x ∧
      deriv (fun t => g (f t)) x = deriv g (f x) * deriv f x := by sorry

end Rudin
