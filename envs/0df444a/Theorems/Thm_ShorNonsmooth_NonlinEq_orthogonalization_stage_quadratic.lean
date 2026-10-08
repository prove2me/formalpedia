-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_orthogonalization_stage_quadratic
-- name    : ShorNonsmooth.NonlinEq.orthogonalization_stage_quadratic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:23:51.541002+00:00
-- url     : https://prove2.me/theorems/cdd9f735-aeee-46ab-b156-0464c6edeb1f
-- title:
--   Theorem 3.9 — one stage of gradient orthogonalization squares the error: $\|x_n\|\le c\|x_0\|^2$
-- statement:
--   Let $x^* = 0$ be the solution of the system of equations
--   $$
--   \psi_i(x) = 0, \qquad i = 1, \dots, n, \qquad x \in E_n,
--   $$
--   where the functions $\psi_i$ are continuously differentiable. Suppose their gradients satisfy the Lipschitz condition in a ball $S_\delta = \{x : \|x\| < \delta\}$: there is a constant $L$ with
--   $$
--   \|g_{\psi_i}(x') - g_{\psi_i}(x'')\| \le L \|x' - x''\| \qquad \text{for all } x', x'' \in S_\delta ,
--   $$
--   and suppose the vectors $g_{\psi_1}(0), \dots, g_{\psi_n}(0)$ are linearly independent, so that the Jacobian determinant $\det J(0)$ is nonzero. Then there exist $\varepsilon > 0$ and a positive constant $c$ such that every stage $x_0^{(r)}, \dots, x_n^{(r)}$ of the gradient orthogonalization method (3.27) with $\|x_0^{(r)}\| \le \varepsilon$ satisfies
--   $$
--   \|x_n^{(r)}\| = \|x_0^{(r+1)}\| \le c\, \|x_0^{(r)}\|^2 .
--   $$
--
--   Since each stage starts where the previous one ended, the stages converge quadratically to the solution once one of them starts within $\min(\varepsilon, 1/(2c))$ of it. Each step of the method uses the value and gradient of a single equation.
--
--   **Formalization Note** $\varepsilon$ and $c$ are chosen before the stage, depending only on the functions $\psi_i$ and the data $\delta, L$; they are uniform over all stages $r$ and all starting points. A stage is `IsOrthStage ψ x` on a sequence $x : \mathbb{N} \to E_n$. Step 1 uses $\|g_{\psi_1}(x_0)\|^2$: the printed (3.27a) omits the square, a misprint (see the definition of the stage).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 65, Theorem 3.9 (method (3.27), Lipschitz condition (3.28))

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 65, Theorem 3.9. Let `x* = 0` be the solution of the system
`ψ_i(x) = 0, i = 1, …, n` (3.26), let the `ψ_i` be continuously differentiable with gradients
satisfying the Lipschitz condition (3.28) with constant `L` in the ball `S_δ = {x : ‖x‖ < δ}`,
and let the vectors `g_{ψ_1}(0), …, g_{ψ_n}(0)` be linearly independent (so `det J(0) ≠ 0`).
Then there are `ε > 0` and a positive constant `c` such that every stage `x_0, …, x_n` of the
gradient orthogonalization method (3.27) with `‖x_0‖ ≤ ε` satisfies
`‖x_n‖ ≤ c ‖x_0‖²`; the next stage starts at `x_0^{(r+1)} = x_n^{(r)}`, so this holds for every
stage `r`. Both `ε` and `c` are chosen before the starting point. Step 1 uses the squared norm
`‖g_{ψ_1}(x_0)‖²` (the printed (3.27a) omits the square; see `IsOrthStage`). -/
theorem orthogonalization_stage_quadratic {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε > 0, ∃ c > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → ‖x n‖ ≤ c * ‖x 0‖ ^ 2 := by sorry

end ShorNonsmooth.NonlinEq
