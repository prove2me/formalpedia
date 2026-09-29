-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_directional_oracle_second_moment
-- name    : RandomGradFree.Accelerated.directional_oracle_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:06.648268+00:00
-- url     : https://prove2.me/theorems/80461530-bb1b-45d2-bbae-a27aa7577953
-- title:
--   Theorem 3.1 — second moment of the directional-derivative oracle, $\mathbb E_u\|g_0(x)\|_*^2 \le (n+4)\|\nabla f(x)\|_*^2$ (Eq. (32))
-- statement:
--   Let $E$ be a real inner product space of dimension $n$, $u$ a standard Gaussian vector in $E$, and $f : E \to \mathbb R$ differentiable at the point $x$. The limiting oracle $B^{-1}g_0(x) = \langle \nabla f(x), u\rangle\, u$ satisfies
--
--   $$
--   \mathbb E_u\big(\|g_0(x)\|_*^2\big) = \mathbb E_u\big(\langle \nabla f(x), u\rangle^2 \|u\|^2\big) \le (n+4)\,\|\nabla f(x)\|_*^2 .
--   $$
--
--   Applied to the Gaussian approximation $f_\mu$, this is the step of the proof of Lemma 5 that controls the variance of the oracle.
--
--   **Formalization Note** The directional derivative is `fderiv ℝ f x u`, and $\|\nabla f(x)\|_*$ is the norm of Mathlib's `gradient f x` (Riesz identification).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 537, Theorem 3, part 1, Eq. (32)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem directional_oracle_second_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, ‖fderiv ℝ f x u • u‖ ^ 2 ∂(stdGaussian E)
      ≤ ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by sorry

end RandomGradFree.Accelerated
