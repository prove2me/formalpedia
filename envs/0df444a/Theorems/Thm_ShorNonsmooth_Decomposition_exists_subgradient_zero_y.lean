-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_exists_subgradient_zero_y
-- name    : ShorNonsmooth.Decomposition.exists_subgradient_zero_y
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:23:23.784659+00:00
-- url     : https://prove2.me/theorems/6d6d9d79-6314-45f1-9bbb-5caddff39392
-- title:
--   Theorem 4.1, proof (p. 95) — $L_U$ has a subgradient at $(\bar x, y(\bar x))$ with null $y$-projection
-- statement:
--   Let $f_0$ and $f_i$, $i = 1,\dots,n$, be jointly convex, and let $U$ be Kuhn–Tucker multipliers of the subproblem (4.3)–(4.4) at $\bar x$ relative to an optimal $\bar y$; in particular $U \ge 0$ and $\bar y$ minimizes $L_U(\bar x, \cdot)$ over all $y$. Then there is a vector $g^x \in E^x_l$ such that $(g^x, 0)$ is a subgradient of the Lagrange function $L_U$ at $(\bar x,\bar y)$:
--   $$
--   L_U(x,y) - L_U(\bar x,\bar y) \ge (g^x, x - \bar x) \qquad \text{for all } (x,y).
--   $$
--   In the book's words, the subdifferential of $L_U$ at $(\bar x,\bar y)$ intersects the hyperplane $y = 0$. This justifies the choice of subgradient in formula (4.6).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 95, proof of Theorem 4.1 ("this is always possible, since L_U(x̄, y(x̄)) = min L(x̄, y)")

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), proof of Theorem 4.1, p. 95 ("this is always possible, since
`L_U(x̄, y(x̄)) = min L(x̄, y)`"): if `f₀` and all `f_i` are jointly convex and `U` are Kuhn–Tucker
multipliers at `xbar` for the optimal point `ybar` (so `ybar` minimizes `L_U(xbar, ·)`), then the Lagrange
function `L_U` has a subgradient at `(xbar, ybar)` whose projection on the `y`-space vanishes. -/
theorem exists_subgradient_zero_y {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m))
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U) :
    ∃ gx : EuclideanSpace ℝ (Fin l), IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0 := by sorry

end ShorNonsmooth.Decomposition
