-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_column_marginal_eq_arc_sum
-- name    : VRPTWColGen92.Bound.column_marginal_eq_arc_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:20.479959+00:00
-- url     : https://prove2.me/theorems/e7f6e800-b92d-4e5a-bed2-dcdf0f51178d
-- title:
--   Sec. 4.1, p. 347 — the marginal cost of a route is the sum of the arc marginal costs (1 − π_c)c_ij − π_i
-- statement:
--   Let $(\pi, \pi_d, \pi_c)$ be any values of the dual variables of the set covering LP, and let $r = (d, i_1, \dots, i_K, d)$ be given by a customer list that does not contain the depot. Then the marginal cost of the column $r$,
--   $$\bar c_r = c_r - \sum_{i \in N\setminus\{d\}} \pi_i\gamma_{ir} - \pi_d - \pi_c c_r,$$
--   equals the sum of the arc marginal costs along $r$:
--   $$\bar c_r = \sum_{k=0}^{K}\big[(1-\pi_c)\,c_{i_k i_{k+1}} - \pi_{i_k}\big],\qquad\text{with } \pi_{i_0} = \pi_d \text{ as } i_0 = d.$$
--
--   This is what lets the pricing subproblem be solved as a shortest path problem with arc costs $\bar c_{ij} = (1-\pi_c)c_{ij} - \pi_i$.
--
--   **Formalization Note.** The identity is algebraic; it needs only that the depot appears at the two ends of the node sequence and nowhere else, so that each customer visit contributes its dual once and the depot contributes $\pi_d$ once. No arc, window or capacity condition is assumed.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 347, Sec. 4.1

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

namespace VRPTWColGen92.Bound
theorem column_marginal_eq_arc_sum {n : ℕ} (I : Instance n) (y : DualPoint n)
    (p : List (Fin (n + 1))) (hp : (0 : Fin (n + 1)) ∉ p) :
    columnMarginal I y p = pathMarginal I y p := by sorry
end VRPTWColGen92.Bound
