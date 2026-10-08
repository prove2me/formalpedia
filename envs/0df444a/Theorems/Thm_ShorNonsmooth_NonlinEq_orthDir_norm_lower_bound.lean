-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_orthDir_norm_lower_bound
-- name    : ShorNonsmooth.NonlinEq.orthDir_norm_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:23:14.320516+00:00
-- url     : https://prove2.me/theorems/25edef21-36a0-4533-ba0f-af15136bd982
-- title:
--   Eq. (3.29) — the orthogonalized gradients are bounded away from zero near the solution
-- statement:
--   Let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ be continuously differentiable and let the gradients $g_{\psi_1}(0), \dots, g_{\psi_n}(0)$ be linearly independent. Then there exist a ball $S_{\delta'} = \{x : \|x\| < \delta'\}$, $\delta' > 0$, and a constant $b > 0$ with the following property: for every stage $x_0, x_1, \dots, x_n$ of the gradient orthogonalization method (3.27) whose points $x_0, \dots, x_{n-1}$ lie in $S_{\delta'}$,
--   $$
--   \|\varphi_{k+1}\| > b, \qquad k = 0, 1, \dots, n-1 .
--   $$
--
--   This keeps the divisions by $\|\varphi_{k+1}\|^2$ in (3.27) well defined and bounded near the solution, and supplies the constant $b$ of the quadratic residual estimate (3.33).
--
--   **Formalization Note** $\delta'$ and $b$ are chosen before the stage, so $b$ is uniform over all stages that stay in $S_{\delta'}$. In the book, $\delta'$ is the radius of a ball on which $|\det\{\partial\psi_i(x_{i-1})/\partial t_j\}| \ge a > 0$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 65-66, Eq. (3.29) (in the proof of Theorem 3.9)

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 66, Eq. (3.29), in the proof of Theorem 3.9. Let the functions `ψ_i` be
continuously differentiable and let the gradients `g_{ψ_i}(0)` be linearly independent. Then
there are a ball `S_{δ'} = {x : ‖x‖ < δ'}` and a constant `b > 0` such that, for every stage
`x_0, …, x_n` of the orthogonalization method (3.27) whose points `x_k`, `k < n`, lie in
`S_{δ'}`, the orthogonalized gradients satisfy `‖φ_{k+1}‖ > b` for `k = 0, …, n − 1`.
The constant `b` is chosen before the stage (it does not depend on the points). -/
theorem orthDir_norm_lower_bound {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ δ' > 0, ∃ b > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      (∀ k < n, x k ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ') →
      ∀ k : Fin n, b < ‖orthDir ψ x k‖ := by sorry

end ShorNonsmooth.NonlinEq
