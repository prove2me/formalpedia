-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_stage_linear_bound_and_growth
-- name    : ShorNonsmooth.NonlinEq.stage_linear_bound_and_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:23:24.428218+00:00
-- url     : https://prove2.me/theorems/5fd31767-bf13-416f-a37a-44a629c07d03
-- title:
--   Eqs. (3.36)–(3.37) — a stage moves $O(\|x_0\|)$ and $f$ grows linearly near the solution
-- statement:
--   Assume the hypotheses of Theorem 3.9: $x^* = 0$ solves the system $\psi_i(x) = 0$, $i = 1, \dots, n$; the $\psi_i$ are continuously differentiable with gradients satisfying the Lipschitz condition (3.28) with constant $L$ on $S_\delta = \{x : \|x\| < \delta\}$; and $g_{\psi_1}(0), \dots, g_{\psi_n}(0)$ are linearly independent. Then there exist a number $\varepsilon_0 > 0$ and two positive constants $c_1, c_2$ such that for every stage $x_0, \dots, x_n$ of the gradient orthogonalization method (3.27) with $\|x_0\| \le \varepsilon_0$:
--
--   1. all points of the stage stay within a constant multiple of $\|x_0\|$,
--   $$
--   \max_{1 \le k \le n} \|x_k\| \le c_1 \|x_0\| ; \tag{3.36}
--   $$
--   2. the merit function $f = \max_i |\psi_i|$ grows at least linearly at the end point,
--   $$
--   f(x_n) = \max_{0 \le k \le n-1} |\psi_{k+1}(x_n)| \ge c_2 \|x_n\| . \tag{3.37}
--   $$
--
--   Together with the estimate $\max_k|\psi_{k+1}(x_n)| = O(\|x_0\|^2)$ obtained from (3.33) and Lemma 3.1, these two statements give Theorem 3.9.
--
--   **Formalization Note** $\varepsilon_0, c_1, c_2$ are chosen before the stage and do not depend on it. $f$ is `maxResidual ψ`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 67, Eqs. (3.36)-(3.37) (in the proof of Theorem 3.9)

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 67, Eqs. (3.36)–(3.37), in the proof of Theorem 3.9. Under the hypotheses
of Theorem 3.9 (`x* = 0` solves `ψ_i(x) = 0`, the `ψ_i` are continuously differentiable with
gradients `L`-Lipschitz on the open ball `S_δ`, and `g_{ψ_1}(0), …, g_{ψ_n}(0)` are linearly
independent) there exist a number `ε₀ > 0` and two positive constants `c₁, c₂` such that, for
every stage `x_0, …, x_n` of the orthogonalization method (3.27) with `‖x_0‖ ≤ ε₀`,
1. `max_{1 ≤ k ≤ n} ‖x_k‖ ≤ c₁ ‖x_0‖` (3.36), and
2. `f(x_n) = max_{0 ≤ k ≤ n−1} |ψ_{k+1}(x_n)| ≥ c₂ ‖x_n‖` (3.37). -/
theorem stage_linear_bound_and_growth {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε₀ > 0, ∃ c₁ > 0, ∃ c₂ > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε₀ →
      (∀ k, 1 ≤ k → k ≤ n → ‖x k‖ ≤ c₁ * ‖x 0‖) ∧ c₂ * ‖x n‖ ≤ maxResidual ψ (x n) := by sorry

end ShorNonsmooth.NonlinEq
