-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_residual_after_step_quadratic
-- name    : ShorNonsmooth.NonlinEq.residual_after_step_quadratic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:23:13.270164+00:00
-- url     : https://prove2.me/theorems/003bd750-1ea6-4572-aa75-8bd7b7a15969
-- title:
--   Eq. (3.33) — after step $k+1$ the residual $\psi_{k+1}$ is quadratically small
-- statement:
--   Let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ be continuously differentiable with gradients satisfying the Lipschitz condition
--   $$
--   \|g_{\psi_i}(x') - g_{\psi_i}(x'')\| \le L \|x' - x''\| \qquad \text{for all } x', x'' \in S_\delta = \{x : \|x\| < \delta\}. \tag{3.28}
--   $$
--   Let $x_0, \dots, x_n$ be a stage of the gradient orthogonalization method (3.27), let $0 \le k \le n-1$, and suppose that $x_k, x_{k+1} \in S_\delta$ and $\|\varphi_{k+1}\| > b$ for a constant $b > 0$. Then
--   $$
--   |\psi_{k+1}(x_{k+1})| \le \frac{L\, \psi_{k+1}^2(x_k)}{\|\varphi_{k+1}\|^2} \le \frac{L}{b^2}\, \psi_{k+1}^2(x_k).
--   $$
--
--   Step $k+1$ is a Newton-type step for the single equation $\psi_{k+1} = 0$ along $\varphi_{k+1}$; the estimate says that this equation is satisfied to second order after the step, which is the first half of the quadratic convergence of Theorem 3.9.
--
--   **Formalization Note** Zero-based indices: `ψ k` is $\psi_{k+1}$ and `orthDir ψ x k` is $\varphi_{k+1}$. The hypotheses $x_k, x_{k+1} \in S_\delta$ are the book's standing assumption in this part of the proof (all points of the stage lie in $S_{\delta'} \subseteq S_\delta$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 66, Eq. (3.33) (in the proof of Theorem 3.9)

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 66, Eq. (3.33), in the proof of Theorem 3.9. Let the functions `ψ_i` be
continuously differentiable with gradients `L`-Lipschitz on the open ball `S_δ` (3.28), and let
`x_0, …, x_n` be a stage of the orthogonalization method (3.27). If, for some step
`k ∈ {0, …, n − 1}`, the points `x_k` and `x_{k+1}` lie in `S_δ` and `‖φ_{k+1}‖ > b > 0`, then
`|ψ_{k+1}(x_{k+1})| ≤ L ψ_{k+1}(x_k)² / ‖φ_{k+1}‖² ≤ (L / b²) ψ_{k+1}(x_k)²`
(book indexing; here `ψ k` is the book's `ψ_{k+1}` and `orthDir ψ x k` the book's `φ_{k+1}`). -/
theorem residual_after_step_quadratic {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x) (k : Fin n)
    (hxk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hxk1 : x (k.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (b : ℝ) (hb : 0 < b) (hφ : b < ‖orthDir ψ x k‖) :
    |ψ k (x (k.val + 1))| ≤ L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2 ∧
      L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2 ≤ L / b ^ 2 * ψ k (x k.val) ^ 2 := by sorry

end ShorNonsmooth.NonlinEq
