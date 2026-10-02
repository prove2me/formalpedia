-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_exists_kuhnTucker_multiplier
-- name    : ShorNonsmooth.Decomposition.exists_kuhnTucker_multiplier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:22:47.246282+00:00
-- url     : https://prove2.me/theorems/d06bf132-8af5-4c72-a63e-b376e9f5c96e
-- title:
--   Theorem 4.1, proof (p. 95) — Kuhn–Tucker multipliers of the subproblem exist under Slater's condition
-- statement:
--   Let $f_0$ and $f_i$, $i = 1,\dots,n$, be jointly convex, fix $\bar x$, and suppose the constraints $f_i(\bar x, y) \le 0$ satisfy the Slater condition: some $y$ has $f_i(\bar x, y) < 0$ for all $i$. If $\bar y$ is an optimal solution of the subproblem $\min_{y \in D(\bar x)} f_0(\bar x,y)$, then there exist multipliers $U = (U_1,\dots,U_n)$ with $U_i \ge 0$, $U_i f_i(\bar x,\bar y) = 0$ for all $i$, and
--   $$
--   L_U(\bar x,\bar y) = \min_{y}\Big[f_0(\bar x,y) + \sum_{i=1}^n U_i f_i(\bar x,y)\Big],
--   $$
--   so that $\Phi(\bar x) = \min_y L_U(\bar x,y) = \max_{U \ge 0}\min_y L_U(\bar x,y)$.
--
--   This is the Kuhn–Tucker theorem applied to the subproblem (4.3)–(4.4); the multipliers it yields are the $U$ of formula (4.6).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 95, proof of Theorem 4.1, first display

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), proof of Theorem 4.1, p. 95 ("By the Kuhn-Tucker theorem …"): for a fixed `xbar`,
if the constraints (4.4) satisfy the Slater condition and `ybar` is an optimal value of `y` in problem
(4.3)–(4.4), then Kuhn–Tucker multipliers `U ≥ 0` exist: complementary slackness holds at `ybar` and
`ybar` minimizes `L_U(xbar, ·)` over all `y`, i.e. `Φ(xbar) = min_y [f₀(xbar, y) + Σ U_i f_i(xbar, y)]`. -/
theorem exists_kuhnTucker_multiplier {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (hslater : SlaterAt f xbar)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar) :
    ∃ U : Fin n → ℝ, IsKuhnTuckerMultiplier f₀ f xbar ybar U := by sorry

end ShorNonsmooth.Decomposition
