-- Prove2me | Theorems.Thm_SchedSurvey_O2_fig_5_2_combined_feasible
-- name    : SchedSurvey.O2.fig_5_2_combined_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:31.534166+00:00
-- url     : https://prove2.me/theorems/831eaade-a910-43c2-a754-79423a74a6cf
-- title:
--   §5.2.1, p. 312, Fig. 5.2 — if T₁ − a_l ≥ T₂ − b_r, the combined schedule J_l, B′, A′, J_r is feasible and ends by T₁ + b_r
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, $T_1 = \sum_j a_j$, $T_2 = \sum_j b_j$, the sets $A = \{J_j \mid a_j \ge b_j\}$ and $B = \{J_j \mid a_j < b_j\}$, two distinct jobs $J_r$, $J_l$ with $a_r \ge \max_{J_j \in A} b_j$ and $b_l \ge \max_{J_j \in B} a_j$, and arbitrary orders of $B' = B - \{J_r, J_l\}$ and $A' = A - \{J_r, J_l\}$. Suppose
--   $$
--   T_1 - a_l \ge T_2 - b_r .
--   $$
--   Run the jobs in the order $J_l, B', A', J_r$ back to back on $M_1$ from time $0$, and in the same order back to back on $M_2$ from time $T_1 + b_r - T_2$ (the jobs of $B' \cup \{J_l\}$ pushed to the right on $M_2$). This schedule of all $n$ jobs is feasible and every operation ends by time $T_1 + b_r$.
--
--   This is the combination of the two blocks of Fig. 5.1 shown in Fig. 5.2; both machines run without idle time from their first to their last job. The final schedules of cases (1) and (2) are obtained from it by moving $J_r$ to the front of $M_2$.
--
--   **Formalization Note** Start times are given by `contigStart` on the list $J_l :: B' \mathbin{+\!\!+} A' \mathbin{+\!\!+} [J_r]$; the length $T_1 + b_r$ is read from Fig. 5.2, where $J_r$ starts on $M_2$ when it ends on $M_1$ at time $T_1$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "Suppose T₁ − a_l ≥ T₂ − b_r … We then combine the two schedules as shown in Fig. 5.2 …", Fig. 5.2

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312, Fig. 5.2: if `T₁ − a_l ≥ T₂ − b_r`, the schedule that runs the jobs in the order
`J_l, B', A', J_r` back to back on `M₁` from time `0` and in the same order back to back on `M₂`
from time `T₁ + b_r − T₂` (the jobs of `B' ∪ {J_l}` pushed to the right) is feasible and completes
by `T₁ + b_r`. -/
theorem fig_5_2_combined_feasible {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (r l : Fin n) (hrl : r ≠ l)
    (hr : ∀ j ∈ setA a b, b j ≤ a r) (hl : ∀ j ∈ setB a b, a j ≤ b l)
    (LA LB : List (Fin n)) (hLA : LA.Nodup) (hLB : LB.Nodup)
    (hLAmem : ∀ j, j ∈ LA ↔ (j ∈ setA a b ∧ j ≠ r ∧ j ≠ l))
    (hLBmem : ∀ j, j ∈ LB ↔ (j ∈ setB a b ∧ j ≠ r ∧ j ≠ l))
    (h52 : T₂ b - b r ≤ T₁ a - a l) :
    IsFeasible a b
        ⟨contigStart a (l :: LB ++ LA ++ [r]),
          fun j => T₁ a + b r - T₂ b + contigStart b (l :: LB ++ LA ++ [r]) j⟩ ∧
      CompletesBy a b
        ⟨contigStart a (l :: LB ++ LA ++ [r]),
          fun j => T₁ a + b r - T₂ b + contigStart b (l :: LB ++ LA ++ [r]) j⟩
        (T₁ a + b r) := by sorry

end SchedSurvey.O2
