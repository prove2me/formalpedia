-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_convex_gradient_isSubgradient
-- name    : ShorNonsmooth.AlmostDiff.convex_gradient_isSubgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:55:54.292596+00:00
-- url     : https://prove2.me/theorems/5771e093-da5f-4c37-87a1-25821186b8a8
-- title:
--   Proof of Theorem 1.15 (p. 18) — the gradient of a convex function is a subgradient
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex and differentiable at a point $x_k$, with gradient $g_f(x_k) = \nabla f(x_k)$. Then for all $x \in E_n$
--
--   $$
--   f(x) - f(x_k) \ge (g_f(x_k),\, x - x_k),
--   $$
--
--   that is, $g_f(x_k)$ is a subgradient of $f$ at $x_k$.
--
--   This is the inequality in the proof of Theorem 1.15 that is passed to the limit along a sequence of points of differentiability to show that almost-gradients of convex functions are subgradients.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, proof of Theorem 1.15, displayed inequality

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, proof of Theorem 1.15, displayed inequality: if a convex function `f` on
`E_n` is differentiable at `x_k`, then for all `x ∈ E_n`,
`f(x) - f(x_k) ≥ (∇f(x_k), x - x_k)`, i.e. the gradient is a subgradient. -/
theorem convex_gradient_isSubgradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xk : EuclideanSpace ℝ (Fin n)) (hxk : DifferentiableAt ℝ f xk) :
    IsSubgradient f xk (gradient f xk) := by sorry

end ShorNonsmooth.AlmostDiff
