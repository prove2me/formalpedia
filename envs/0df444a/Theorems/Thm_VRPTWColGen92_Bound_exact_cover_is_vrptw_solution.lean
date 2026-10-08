-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_exact_cover_is_vrptw_solution
-- name    : VRPTWColGen92.Bound.exact_cover_is_vrptw_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:08.127535+00:00
-- url     : https://prove2.me/theorems/859a02fb-d250-4d29-b43c-b5c68da9c49f
-- title:
--   Sec. 5, p. 348 — an integral LP solution covering each customer exactly once is a VRPTW solution of the same cost
-- statement:
--   Let $(x, X_d, X_c)$ be a feasible point of the LP relaxation of the set covering type model (1)–(6) over the paths of the second model (resource-feasible paths, customers possibly repeated). Suppose that $x$ is integral, $x_r \in \mathbb N$ for every column $r$, and that every customer is covered exactly once:
--   $$\sum_r \gamma_{ir} x_r = 1\qquad (i\in N\setminus\{d\}).$$
--   Then the set of columns with $x_r > 0$ is a VRPTW solution (a set of feasible routes, each visiting every customer at most once, covering every customer exactly once), and its cost equals the objective value $\sum_r c_r x_r$.
--
--   In particular such a point uses only elementary routes, even though the LP allows columns with repeated customers.
--
--   **Formalization Note.** The statement is over second-model paths, which contain the 2-cycle-free paths, so it applies to the LP over 2-cycle-free paths as well.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 348, Sec. 5

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

namespace VRPTWColGen92.Bound
theorem exact_cover_is_vrptw_solution {n : ℕ} (I : Instance n)
    (z : LPPoint n) (hz : LPFeasible I {p | IsPath I p} z)
    (hint : ∀ p, ∃ m : ℕ, z.x p = m)
    (hexact : ∀ i : Fin (n + 1), i ≠ 0 →
      ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1) :
    IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z := by sorry
end VRPTWColGen92.Bound
