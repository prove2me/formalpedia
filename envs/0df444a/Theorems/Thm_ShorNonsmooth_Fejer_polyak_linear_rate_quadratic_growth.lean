-- Prove2me | Theorems.Thm_ShorNonsmooth_Fejer_polyak_linear_rate_quadratic_growth
-- name    : ShorNonsmooth.Fejer.polyak_linear_rate_quadratic_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:30:46.502392+00:00
-- url     : https://prove2.me/theorems/5cd9a644-dd50-4b48-b944-c89b9c1a7432
-- title:
--   Theorem 2.12 — Polyak's method converges geometrically under quadratic growth and Lipschitz gradient
-- statement:
--   Let $f$ be convex on $E_n$ with a minimum point $x^*$ and $f^* = f(x^*)$, and suppose that for some $m > 0$
--   $$
--   f(x) - f^* \ge m\,\|x - x^*\|^2 \qquad \text{for all } x .
--   $$
--   Suppose further that $f$ is differentiable on the ball $\|x - x^*\| \le \|x_0 - x^*\|$ and its gradient is Lipschitz continuous there with a constant $L > 0$. Let $0 < \gamma < 2$ and let $\{x_k\}$ be generated from $x_0$ by Polyak's method (2.32) with $c = f^*$, for any subgradient selection $g_f$. Then
--   $$
--   \|x_k - x^*\| \le q^k\, \|x_0 - x^*\| \quad (k = 0, 1, \dots), \qquad q = \Bigl(1 - \gamma(2-\gamma)\frac{m^2}{L^2}\Bigr)^{1/2} < 1 .
--   $$
--
--   Under quadratic growth and a smooth gradient near the minimum, Polyak's step with the exact optimal value converges at the rate of a geometric progression.
--
--   **Formalization Note** The book calls $f$ "strongly convex"; the only property its proof uses is the displayed growth inequality, and the statement is made for every convex $f$ satisfying it. The square root is `Real.sqrt`; its argument is nonnegative whenever $x_0 \neq x^*$ (it then follows from the hypotheses that $m \le L$), and when $x_0 = x^*$ the method never moves. The range $0 < \gamma < 2$ is the section's standing range (Theorem 2.11). The recursion $x_{k+1} = \varphi_c(x_k)$ is a hypothesis on the sequence.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 38, Theorem 2.12

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology

namespace ShorNonsmooth.Fejer

/-- Shor (1985), p. 38, Theorem 2.12. Let `f` be convex on `E_n` with minimum point `x*`,
`f* = f(x*)`, satisfying `f(x) - f* ≥ m ‖x - x*‖²` for some `m > 0` and all `x`, and let `f` be
differentiable with gradient Lipschitz continuous with constant `L > 0` on the ball
`‖x - x*‖ ≤ ‖x₀ - x*‖`. Then Polyak's method (2.32) with `c = f*` and `0 < γ < 2`, for any
subgradient selection, satisfies `‖x_k - x*‖ ≤ q^k ‖x₀ - x*‖` for all `k`, where
`q = (1 - γ(2 - γ) m² / L²)^{1/2} < 1`. -/
theorem polyak_linear_rate_quadratic_growth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hgrowth : ∀ x, f x - f xstar ≥ m * ‖x - xstar‖ ^ 2)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) = polyakStep f g (f xstar) γ (x k))
    (hdiff : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖, DifferentiableAt ℝ f z)
    (hLip : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
      ∀ w ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
        ‖gradient f z - gradient f w‖ ≤ L * ‖z - w‖) :
    (∀ k : ℕ, ‖x k - xstar‖ ≤
        Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) ^ k * ‖x 0 - xstar‖) ∧
      Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) < 1 := by sorry

end ShorNonsmooth.Fejer
