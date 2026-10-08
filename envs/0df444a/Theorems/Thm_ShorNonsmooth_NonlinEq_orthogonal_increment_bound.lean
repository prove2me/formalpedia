-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_orthogonal_increment_bound
-- name    : ShorNonsmooth.NonlinEq.orthogonal_increment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:08:24.695105+00:00
-- url     : https://prove2.me/theorems/b4ccaed6-714a-4bb0-b056-550719269020
-- title:
--   Lemma 3.1 — a step orthogonal to $g_{\psi_i}(x_1)$ changes $\psi_i$ by at most $Lh(h+d)$
-- statement:
--   Let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ be continuously differentiable with gradients satisfying the Lipschitz condition (3.28) with constant $L$ on the ball $S_\delta = \{x : \|x\| < \delta\}$. Let $x_1, x_2 \in E_n$, let $\xi$ be a vector with $\|\xi\| = 1$ and $(g_{\psi_i}(x_1), \xi) = 0$ for some $i$, $1 \le i \le n$, and let $h > 0$. If $x_1, x_2, x_2 + h\xi \in S_\delta$, then
--   $$
--   |\psi_i(x_2 + h\xi) - \psi_i(x_2)| \le L h (h + d), \qquad d = \|x_1 - x_2\|.
--   $$
--
--   In the proof of Theorem 3.9 the later steps of a stage move along directions orthogonal to earlier gradients; the lemma shows that they spoil the equations already solved only by a second-order amount.
--
--   **Formalization Note** $(\cdot,\cdot)$ is the Euclidean inner product `inner ℝ`, $S_\delta$ is the open ball `Metric.ball 0 δ`, and the Lipschitz condition is assumed for all $i$ as in (3.28).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 66-67, Lemma 3.1

import Mathlib

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 66–67, Lemma 3.1. Let the functions `ψ_i` be continuously differentiable
(standing assumption of (3.26)) and let their gradients be `L`-Lipschitz on the open ball
`S_δ = {x : ‖x‖ < δ}` (3.28). Let `x₁, x₂` be two points and `ξ` a unit vector with
`(g_{ψ_i}(x₁), ξ) = 0` for some `i`, and `h > 0`. If `x₁, x₂, x₂ + hξ ∈ S_δ` then
`|ψ_i(x₂ + hξ) − ψ_i(x₂)| ≤ L h (h + d)` with `d = ‖x₁ − x₂‖`. -/
theorem orthogonal_increment_bound {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (i : Fin n) (x₁ x₂ ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (horth : inner ℝ (gradient (ψ i) x₁) ξ = 0) (h : ℝ) (hh : 0 < h)
    (hx₁ : x₁ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hx₂ : x₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hx₂h : x₂ + h • ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :
    |ψ i (x₂ + h • ξ) - ψ i x₂| ≤ L * h * (h + ‖x₁ - x₂‖) := by sorry

end ShorNonsmooth.NonlinEq
