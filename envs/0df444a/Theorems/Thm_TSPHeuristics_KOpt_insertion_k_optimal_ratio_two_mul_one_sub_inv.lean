-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_insertion_k_optimal_ratio_two_mul_one_sub_inv
-- name    : TSPHeuristics.KOpt.insertion_k_optimal_ratio_two_mul_one_sub_inv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:02:22.237412+00:00
-- url     : https://prove2.me/theorems/4b4991a0-adad-4fb8-9431-f03a7e61ccff
-- title:
--   Corollary to Theorem 6 — nearest and cheapest insertion can return a $k$-optimal tour with INSERT/OPTIMAL $= 2(1-1/n)$ when $4k\le n$
-- statement:
--   Let $n\ge 6$ and let $k$ be a natural number with $4k\le n$. There is a traveling salesman graph $(N,d)$ on $n$ nodes with $\mathrm{OPTIMAL}>0$ such that
--
--   1. some run of nearest insertion on $(N,d)$ returns a tour $T_n$ that is $k$-optimal and satisfies
--   $$\frac{\mathrm{INSERT}}{\mathrm{OPTIMAL}}=2\left(1-\frac1n\right),$$
--   2. some run of cheapest insertion on the same $(N,d)$ returns a tour with the same two properties.
--
--   Thus even when nearest or cheapest insertion happens to return a tour that no $k$-change can improve, its length can be as large as the worst-case guarantee $2(1-1/n)\cdot$OPTIMAL of these methods: local optimality certifies nothing better.
--
--   **Formalization Note** The ratio is multiplied out: `cycleLength d (T n) = 2 * (1 - 1/n) * optimal d`, with OPTIMAL the true minimum over all tours. The conjunct `0 < optimal d` is the paper's standing assumption (1.1) (p. 564); without it the zero distance would satisfy everything trivially. The hypothesis $n\ge 6$ is **added** to the printed Corollary ("for any k and n such that 4·k ≦ n"): its proof is the example of Theorem 5, which the paper establishes only for $n\ge 6$, and for $k=0$, $n=3$ the printed statement is false (every tour on three nodes is optimal). $k$-optimality compares the returned tour with every tour at edge difference exactly $k$. Both methods are stated on the same graph, which is what the proof gives.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 581, Corollary to Theorem 6 (with n ≥ 6 from Theorem 5, p. 575)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

namespace TSPHeuristics.KOpt

theorem insertion_k_optimal_ratio_two_mul_one_sub_inv (n k : ℕ) (hn : 6 ≤ n) (hk : 4 * k ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        IsKOptimal d k (T n) ∧ TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by sorry

end TSPHeuristics.KOpt
