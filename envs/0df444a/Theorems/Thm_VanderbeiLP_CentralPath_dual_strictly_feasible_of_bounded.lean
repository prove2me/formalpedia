-- Prove2me | Theorems.Thm_VanderbeiLP_CentralPath_dual_strictly_feasible_of_bounded
-- name    : VanderbeiLP.CentralPath.dual_strictly_feasible_of_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:28:07.015986+00:00
-- url     : https://prove2.me/theorems/ea250462-c980-46c8-8c7a-d2de8c9f57aa
-- title:
--   Exercise 10.7 — interior solutions: a bounded feasible primal has a strictly positive dual feasible point
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$, and consider the linear program "maximize $c^T x$ subject to $Ax \le b$, $x \ge 0$" with its dual "minimize $b^T y$ subject to $A^T y - z = c$, $y, z \ge 0$". If the primal has feasible solutions and its set of feasible solutions
--
--   $$\{x \in \mathbb{R}^n : Ax \le b,\ x \ge 0\}$$
--
--   is bounded, then there is a strictly positive dual feasible solution: vectors $y \in \mathbb{R}^m$ and $z \in \mathbb{R}^n$ with
--
--   $$A^T y - z = c, \qquad y > 0, \qquad z > 0.$$
--
--   Corollary 17.3 derives existence of the central path from Theorem 17.2 and this statement: a bounded primal with nonempty interior supplies both interiors that Theorem 17.2 asks for.
--
--   **Formalization Note** "Bounded" is `Bornology.IsBounded` of the primal feasible set in $\mathbb{R}^n$ (equivalently, of the region of pairs $(x, w)$, since $w = b - Ax$). The feasibility hypothesis is needed: an empty feasible set is bounded, and for $A = (0)$, $b = (-1)$, $c = (1)$ no dual point with $y, z > 0$ exists. The objective $c$ is arbitrary.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 150, Exercise 10.7 (PDF p. 163); problem form (10.9)–(10.10), p. 147 (PDF p. 160)

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology

namespace VanderbeiLP.CentralPath

/-- Exercise 10.7 (p. 150). If the LP `maximize cᵀx s.t. Ax ≤ b, x ≥ 0` has feasible solutions and
its set of feasible solutions is bounded, then there is a strictly positive dual feasible solution:
`Aᵀy − z = c` with `y > 0` and `z > 0`. -/
theorem dual_strictly_feasible_of_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (primalFeasibleSet A b).Nonempty)
    (hbdd : Bornology.IsBounded (primalFeasibleSet A b)) :
    DualStrictlyFeasible A c := by sorry

end VanderbeiLP.CentralPath
