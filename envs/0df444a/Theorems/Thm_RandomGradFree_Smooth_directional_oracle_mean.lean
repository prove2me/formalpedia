-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_directional_oracle_mean
-- name    : RandomGradFree.Smooth.directional_oracle_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:30:38.433639+00:00
-- url     : https://prove2.me/theorems/49e29d6b-d195-465f-9f87-4f434c5776e9
-- title:
--   Section 2, Eq. (25) — $\mathbb E_u \langle\nabla f(x), u\rangle u = \nabla f(x)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $u$ a standard Gaussian vector in $E$, and $f : E \to \mathbb R$ differentiable at $x$. Then
--
--   $$
--   \nabla f_0(x) = \mathbb E_u\big[\langle \nabla f(x), u\rangle\, u\big] = \nabla f(x).
--   $$
--
--   Thus the limiting oracle $g_0(x) = f'(x,u)Bu$ is an unbiased estimate of the gradient at points of differentiability; this is the $\mu = 0$ counterpart of Eq. (21) and is what the analysis of $\mathcal{RG}_0$ uses.
--
--   **Formalization Note** $f'(x,u) = \langle\nabla f(x), u\rangle$ is written as `fderiv ℝ f x u`; the integrand is exactly `oracle f 0 x u`.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 535, Section 2, Eq. (25)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem directional_oracle_mean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, fderiv ℝ f x u • u ∂(stdGaussian E) = gradient f x := by sorry

end RandomGradFree.Smooth
