-- Prove2me | Theorems.Thm_VanderbeiLP_CentralPath_central_path_exists_unique
-- name    : VanderbeiLP.CentralPath.central_path_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:38:48.322867+00:00
-- url     : https://prove2.me/theorems/51432543-7d0d-49fd-838b-cb7be8d82e3b
-- title:
--   Corollary 17.3 — existence and uniqueness of the primal–dual central path point for each $\mu > 0$
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$. Suppose that the primal feasible set has nonempty interior and is bounded, that is,
--
--   1. there is $(\bar x, \bar w)$ with $A\bar x + \bar w = b$, $\bar x > 0$, $\bar w > 0$, and $\{x : Ax \le b,\ x \ge 0\}$ is bounded;
--
--   or, for that matter, that the dual feasible set has nonempty interior and is bounded, that is,
--
--   2. there is $(\bar y, \bar z)$ with $A^T \bar y - \bar z = c$, $\bar y > 0$, $\bar z > 0$, and $\{y : A^T y \ge c,\ y \ge 0\}$ is bounded.
--
--   Then for each $\mu > 0$ there exists a unique solution $(x_\mu, w_\mu, y_\mu, z_\mu)$ with $x_\mu, w_\mu, y_\mu, z_\mu > 0$ to the system (17.6)
--
--   $$Ax + w = b, \qquad A^T y - z = c, \qquad XZe = \mu e, \qquad YWe = \mu e.$$
--
--   The curve $\{(x_\mu, w_\mu, y_\mu, z_\mu) : \mu > 0\}$ is the primal–dual central path, which path-following interior-point methods track toward an optimal solution.
--
--   **Formalization Note** The hypothesis is the disjunction of the primal and the dual versions; the book states the primal one and adds the dual one in a parenthesis. Solutions of (17.6) are required to be strictly positive: (17.6) is derived on p. 263 from the barrier problem, whose domain is $x > 0$, $w > 0$ (and then $y = \mu W^{-1}e > 0$, $z = \mu X^{-1} e > 0$), and Exercise 17.3 (p. 267) states the same system with $x, y, z, w > 0$ explicitly. Without the positivity, sign-flipped solutions of $x_j z_j = \mu$, $y_i w_i = \mu$ are not excluded and uniqueness is not the book's claim.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 266, Corollary 17.3 (PDF p. 276); system (17.6), p. 263 (PDF p. 273); positivity as in Exercise 17.3, p. 267 (PDF p. 277)

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Corollary 17.3 (p. 266). If the primal feasible set has nonempty interior and is bounded (or
the dual feasible set has nonempty interior and is bounded), then for each `μ > 0` the system
(17.6) has a unique solution `(x_μ, w_μ, y_μ, z_μ)` with `x_μ, w_μ, y_μ, z_μ > 0`. -/
theorem central_path_exists_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (h : (PrimalStrictlyFeasible A b ∧ Bornology.IsBounded (primalFeasibleSet A b)) ∨
      (DualStrictlyFeasible A c ∧ Bornology.IsBounded (dualFeasibleSet A c))) :
    ∀ μ : ℝ, 0 < μ →
      ∃! p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
        IsCentralPathPoint A b c μ p.1 p.2.1 p.2.2.1 p.2.2.2 := by sorry

end VanderbeiLP.CentralPath
