-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_no_overcovering_of_strict_triangle
-- name    : VRPTWColGen92.Bound.no_overcovering_of_strict_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:10.293283+00:00
-- url     : https://prove2.me/theorems/98701ac4-47f3-43f1-b654-72f9f70400d8
-- title:
--   Sec. 5, p. 348 — under the strict triangle inequality an optimal LP solution over routes covers no customer more than once
-- statement:
--   This is a pinned-down version of the paper's remark that overcovering "is guaranteed not to occur if the cost matrix satisfies the strict triangle inequality".
--
--   Consider a VRPTW instance in which
--   1. the costs satisfy the strict triangle inequality: $c_{ik} < c_{ij} + c_{jk}$ for pairwise distinct nodes $i, j, k$;
--   2. every ordered pair of distinct nodes is an arc;
--   3. $c_{ij} > 0$ for $i \ne j$;
--   4. the durations satisfy $t_{ik} \le t_{ij} + t_{jk}$ for pairwise distinct $i, j, k$;
--   5. all demands are nonnegative.
--
--   Let $(x, X_d, X_c)$ be an optimal solution of the LP relaxation of the set covering type model (1)–(6) over the set $R$ of feasible routes. Then every customer is covered exactly once:
--   $$\sum_{r\in R}\gamma_{ir}x_r = 1\qquad(i \in N\setminus\{d\}).$$
--
--   **Formalization Note.** Conditions 2–5 are not stated on the page and are added: removing a customer from a route (a shortcut) must give a route again (complete arcs, the time triangle inequality so the shortened route stays schedulable, nonnegative demands so its load does not grow) of strictly smaller cost (positive costs exclude a zero-cost one-customer route). The statement is over elementary routes; over columns with repeated customers, removing one visit can create a 2-cycle or a loop.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 348, Sec. 5

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

namespace VRPTWColGen92.Bound
theorem no_overcovering_of_strict_triangle {n : ℕ} (I : Instance n)
    (htri : ∀ i j k : Fin (n + 1), i ≠ j → j ≠ k → i ≠ k → I.c i k < I.c i j + I.c j k)
    (harc : ∀ i j : Fin (n + 1), i ≠ j → I.arc i j)
    (hcpos : ∀ i j : Fin (n + 1), i ≠ j → 0 < I.c i j)
    (httri : ∀ i j k : Fin (n + 1), i ≠ j → j ≠ k → i ≠ k → I.t i k ≤ I.t i j + I.t j k)
    (hq : ∀ i : Fin (n + 1), 0 ≤ I.q i)
    (z : LPPoint n) (hz : LPOptimal I {p | IsRoute I p} z) :
    ∀ i : Fin (n + 1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1 := by sorry
end VRPTWColGen92.Bound
