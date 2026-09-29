-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_6_proof_circle_subtour_k_optimal
-- name    : TSPHeuristics.KOpt.theorem_6_proof_circle_subtour_k_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:01:02.809407+00:00
-- url     : https://prove2.me/theorems/8cb1110d-9b79-4de4-be71-01ab25eb5cea
-- title:
--   Proof of Theorem 6 — the insertion tour $T_n$ on the circle is $k$-optimal for $k\le n/4$
-- statement:
--   Let $n\ge 6$ and $k$ a natural number with $4k\le n$. On the circle graph $(N_n,d_n)$ the tour $T_n$ produced by the insertion runs of Theorem 5 is $k$-optimal: no tour whose edge set differs from that of $T_n$ in exactly $k$ edges is shorter than $T_n$.
--
--   In the paper's argument, deleting $k$ edges of $T_n$ lowers the length by at most $2k$, while the at least $n-2k$ unit edges whose counts were not decreased must each change parity, so the length rises by at least $n-2k$; an improvement would need $2k>n-2k$.
--
--   **Formalization Note** $T_n$ is the list `circleSubtour n n` (0-based nodes); $k$-optimality compares $T_n$ with every tour at edge difference exactly $k$ (`IsKOptimal`). The hypothesis $n\ge 6$ is the range in which $T_n$ is the insertion tour of Theorem 5.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 580, proof of Theorem 6, last paragraph ('Now suppose that tour T_n is changed by a k-change to an odd tour …')

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_circle_subtour_k_optimal (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    IsKOptimal (cycDist n) k (circleSubtour n n) := by sorry

end TSPHeuristics.KOpt
