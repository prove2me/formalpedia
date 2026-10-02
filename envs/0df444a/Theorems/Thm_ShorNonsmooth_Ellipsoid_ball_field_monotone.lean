-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_ball_field_monotone
-- name    : ShorNonsmooth.Ellipsoid.ball_field_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:18:47.613073+00:00
-- url     : https://prove2.me/theorems/536ce06c-4aa0-41c9-9442-6e23dff058f2
-- title:
--   Eq. (3.62) — a vector field for minimizing a convex function on a ball
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex, let $g_f(x)$ be a subgradient of $f$ at $x$ for every $x$, and let $x^*$ be a minimum point of $f$ on the ball $S(x_0, R) = \{x : \|x - x_0\| \le R\}$. Define the vector field
--   $$
--   g(x) = \begin{cases} g_f(x) & \text{if } x \in S(x_0, R), \\[2pt] \dfrac{x - x_0}{\|x - x_0\|} & \text{if } x \notin S(x_0, R). \end{cases}
--   $$
--   Then
--   $$
--   (g(x), x - x^*) \ge 0 \qquad \text{for all } x \in E_n .
--   $$
--
--   The field makes the algorithm (3.57)–(3.60) applicable to constrained minimization on a ball: by Theorem 3.14, $x^*$ remains in ellipsoids whose volume decreases with ratio $q_n$.
--
--   **Formalization Note** The subgradient property is $f(y) - f(x) \ge (g_f(x), y - x)$ for all $x, y$. The book's intermediate estimate for $x \notin S(x_0,R)$ prints $\|x - x_0\|(\|x - x_0\| + \|x^* - x_0\|)$ where $\|x - x_0\|(\|x - x_0\| - \|x^* - x_0\|)$ is meant; only the conclusion is stated.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 88, §3.8.1, Eq. (3.62)

import Mathlib

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), p. 88, (3.62). Let `f` be convex on `E_n`, `g_f` a subgradient selection of `f`,
and `x*` a minimum point of `f` on the ball `S(x₀, R) = {x : ‖x - x₀‖ ≤ R}`. The field
`g(x) = g_f(x)` for `x ∈ S(x₀, R)`, `g(x) = (x - x₀)/‖x - x₀‖` for `x ∉ S(x₀, R)`, satisfies
`(g(x), x - x*) ≥ 0` for all `x`. (The book's intermediate bound
`‖x - x₀‖(‖x - x₀‖ + ‖x* - x₀‖)` is a misprint for `‖x - x₀‖(‖x - x₀‖ - ‖x* - x₀‖)`; only the
conclusion is stated.) -/
theorem ball_field_monotone {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (gf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hgf : ∀ x y : EuclideanSpace ℝ (Fin n), f y - f x ≥ inner ℝ (gf x) (y - x))
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hxstar : xstar ∈ Metric.closedBall x₀ R)
    (hmin : ∀ x ∈ Metric.closedBall x₀ R, f xstar ≤ f x)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg_in : ∀ x ∈ Metric.closedBall x₀ R, g x = gf x)
    (hg_out : ∀ x ∉ Metric.closedBall x₀ R, g x = ‖x - x₀‖⁻¹ • (x - x₀)) :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ (g x) (x - xstar) := by sorry

end ShorNonsmooth.Ellipsoid
