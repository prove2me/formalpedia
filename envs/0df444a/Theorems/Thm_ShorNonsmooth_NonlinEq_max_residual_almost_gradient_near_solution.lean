-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_max_residual_almost_gradient_near_solution
-- name    : ShorNonsmooth.NonlinEq.max_residual_almost_gradient_near_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:21:57.665001+00:00
-- url     : https://prove2.me/theorems/e816baae-7e8d-45ed-a260-8035c5cda886
-- title:
--   Theorem 3.8 — near a regular solution, $(g_f(x),x-x^*)$ is within a factor $1\pm\delta$ of $f(x)$
-- statement:
--   Let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ and $f(x) = \max_{1\le i\le n} |\psi_i(x)|$. Consider the **regular case**: the minimum value of $f$ is $f^* = 0$, attained at the optimal point $x^*$ (so $\psi_i(x^*) = 0$ for all $i$); the functions $\psi_i$ are continuously differentiable in a neighborhood of $x^*$; and the Jacobian $J(x^*) = \{\partial\psi_i/\partial t_j\}$ is nonsingular. Then for any $\delta > 0$ there is a neighborhood of $x^*$ such that
--   $$
--   (1-\delta)\, f(x) \le (g_f(x),\, x - x^*) \le (1+\delta)\, f(x)
--   $$
--   for all $x$ in that neighborhood and every almost-gradient $g_f(x)$ of $f$ at $x$.
--
--   Inequalities of this form, with constants $M = 1+\delta$, $N = 1-\delta$, are the hypotheses (3.18) of the space-dilation method of Theorem 3.3; the theorem shows that near a regular solution they hold with $M, N$ arbitrarily close to $1$, which permits dilation coefficients close to the extreme value used by the orthogonalization method.
--
--   **Formalization Note** The neighborhood depends on $\delta$ and is a set in `nhds xstar`; it contains $x^*$, where both sides vanish. Nonsingularity is `(jacobianMatrix ψ xstar).det ≠ 0`, and continuous differentiability near $x^*$ is `ContDiffOn ℝ 1 (ψ i) U` on a neighborhood `U` of $x^*$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 63, Theorem 3.8 (regular case defined on p. 63)

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 63, Theorem 3.8. The regular case (p. 63): `f(x) = max_i |ψ_i(x)|` (3.24)
has minimum value `f* = 0` at the optimal point `x*` (all `ψ_i(x*) = 0`), the functions `ψ_i` are
continuously differentiable in a neighborhood of `x*`, and the Jacobian `J(x*)` is nonsingular.
Then for any `δ > 0` there is a neighborhood of `x*` such that for every `x` in it and every
almost-gradient `g_f(x)` of `f` at `x`,
`(1 − δ) f(x) ≤ (g_f(x), x − x*) ≤ (1 + δ) f(x)`. -/
theorem max_residual_almost_gradient_near_solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (hroot : ∀ i, ψ i xstar = 0) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ nhds xstar) (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
      (1 - δ) * maxResidual ψ x ≤ inner ℝ g (x - xstar) ∧
        inner ℝ g (x - xstar) ≤ (1 + δ) * maxResidual ψ x := by sorry

end ShorNonsmooth.NonlinEq
