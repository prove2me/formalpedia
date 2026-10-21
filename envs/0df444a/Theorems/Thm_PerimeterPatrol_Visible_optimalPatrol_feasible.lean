-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_optimalPatrol_feasible
-- name    : PerimeterPatrol.Visible.optimalPatrol_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:49.740986+00:00
-- url     : https://prove2.me/theorems/a3ce101a-a025-4828-ba30-47af8e904103
-- title:
--   Theorem 2, p. 7 — the blue–red schedule is a feasible mixed strategy: long-run rate λ almost surely (implicit in the statement, condition (1))
-- statement:
--   Let $\lambda > 0$ and $t > 0$. The blue–red schedule $\mu^*$ of Theorem 2 (blue patrollers at $jt + k\Delta$, $\Delta = t/\lceil \lambda t \rceil$, $1 \le k \le \lfloor \lambda t \rfloor$; a red patroller at each $jt$ independently with probability $\lambda t - \lfloor \lambda t \rfloor$) is a feasible mixed strategy of the game $\Gamma(\lambda, t, p)$:
--
--   1. $\mu^*$ is a probability measure on dispatch sequences, and
--   2. $\mu^*$-almost every sequence is nondecreasing, starts at a time $\ge 0$, and satisfies condition (1):
--
--   $$\lim_{T\to\infty} \frac{\#\{n : s_n \le T\}}{T} = \lambda .$$
--
--   The paper does not check this separately: it is implicit in calling the schedule the defender's optimal strategy in a game whose strategies must satisfy (1). The long-run rate is $\lfloor \lambda t \rfloor / t$ from the blue patrollers plus $(\lambda t - \lfloor \lambda t \rfloor)/t$ from the red ones, the latter only almost surely.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, pp. 2, 6–7, Theorem 2 (schedule) with condition (1)

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

namespace PerimeterPatrol.Visible
theorem optimalPatrol_feasible (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) : IsMixedStrategy lam (optimalPatrol lam t) := by sorry
end PerimeterPatrol.Visible
