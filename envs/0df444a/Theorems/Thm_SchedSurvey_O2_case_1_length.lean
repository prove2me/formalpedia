-- Prove2me | Theorems.Thm_SchedSurvey_O2_case_1_length
-- name    : SchedSurvey.O2.case_1_length
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:32.308984+00:00
-- url     : https://prove2.me/theorems/67f0050a-a510-49f2-a514-54b1c8c2ee1c
-- title:
--   §5.2.1, p. 312, case (1) — if T₁ − a_l ≥ T₂ − b_r and a_r ≤ T₂ − b_r, some feasible schedule has length ≤ max{T₁, T₂}
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, $T_1 = \sum_j a_j$, $T_2 = \sum_j b_j$, the sets $A = \{J_j \mid a_j \ge b_j\}$ and $B = \{J_j \mid a_j < b_j\}$, and two distinct jobs $J_r$, $J_l$ with $a_r \ge \max_{J_j \in A} b_j$ and $b_l \ge \max_{J_j \in B} a_j$. If
--   $$
--   T_1 - a_l \ge T_2 - b_r \qquad\text{and}\qquad a_r \le T_2 - b_r ,
--   $$
--   then there is a feasible schedule of all jobs whose length is at most
--   $$
--   \max\{T_1, T_2\}.
--   $$
--
--   This is case (1) of the survey's construction (Fig. 5.3, where $J_r$ is moved to the first position on $M_2$). Since $\max\{T_1, T_2\}$ is a lower bound on every schedule's length, the schedule is optimal.
--
--   **Formalization Note** "Length at most $L$" is `CompletesBy … L`: every operation ends by $L$. The statement asserts the length, not the exact start times of Fig. 5.3, which is drawn for $T_1 \ge T_2$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, case (1), Fig. 5.3

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312, case (1): if `T₁ − a_l ≥ T₂ − b_r` and `a_r ≤ T₂ − b_r`, there is a feasible
schedule of length at most `max{T₁, T₂}` (Fig. 5.3). -/
theorem case_1_length {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (r l : Fin n) (hrl : r ≠ l)
    (hr : ∀ j ∈ setA a b, b j ≤ a r) (hl : ∀ j ∈ setB a b, a j ≤ b l)
    (h52 : T₂ b - b r ≤ T₁ a - a l) (h1 : a r ≤ T₂ b - b r) :
    ∃ S : Schedule n, IsFeasible a b S ∧ CompletesBy a b S (max (T₁ a) (T₂ b)) := by sorry

end SchedSurvey.O2
