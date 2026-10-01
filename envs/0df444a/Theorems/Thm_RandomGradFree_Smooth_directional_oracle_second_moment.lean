-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_directional_oracle_second_moment
-- name    : RandomGradFree.Smooth.directional_oracle_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:59:01.563796+00:00
-- url     : https://prove2.me/theorems/edb1999a-21d6-4bec-a972-8548f070b142
-- title:
--   Theorem 3.1 (32) — $\mathbb E_u\|g_0(x)\|_*^2 \le (n+4)\|\nabla f(x)\|_*^2$
-- statement:
--   Let $E$ be a real inner product space of finite dimension $n$, $u$ a standard Gaussian vector in $E$, and $f : E \to \mathbb R$ differentiable at $x$. Let $g_0(x) = f'(x,u)Bu$ be the limiting random oracle of (30). Then
--
--   $$
--   \mathbb E_u\big(\|g_0(x)\|_*^2\big) \le (n+4)\,\|\nabla f(x)\|_*^2 .
--   $$
--
--   This variance bound, of order $n$ rather than the naive $(n+4)^2$, is what gives the random gradient method $\mathcal{RG}_0$ its linear dependence on the dimension.
--
--   **Formalization Note** $\|g_0(x)\|_* = \|f'(x,u)\,u\|$ with $f'(x,u)$ written as `fderiv ℝ f x u`; no convexity is assumed, as in part 1 of the theorem.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 537, Theorem 3, part 1, Eq. (32)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem directional_oracle_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, ‖fderiv ℝ f x u • u‖ ^ 2 ∂(stdGaussian E)
      ≤ ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by sorry

end RandomGradFree.Smooth
