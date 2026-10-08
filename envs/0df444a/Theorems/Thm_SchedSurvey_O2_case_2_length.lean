-- Prove2me | Theorems.Thm_SchedSurvey_O2_case_2_length
-- name    : SchedSurvey.O2.case_2_length
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:47.344142+00:00
-- url     : https://prove2.me/theorems/8f3809bd-f0fb-4a61-87c0-e98fdb7fc54e
-- title:
--   §5.2.1, p. 312, case (2) — if T₁ − a_l ≥ T₂ − b_r and a_r > T₂ − b_r, some feasible schedule has length ≤ max{T₁, a_r + b_r}
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, $T_1 = \sum_j a_j$, $T_2 = \sum_j b_j$, the sets $A = \{J_j \mid a_j \ge b_j\}$ and $B = \{J_j \mid a_j < b_j\}$, and two distinct jobs $J_r$, $J_l$ with $a_r \ge \max_{J_j \in A} b_j$ and $b_l \ge \max_{J_j \in B} a_j$. If
--   $$
--   T_1 - a_l \ge T_2 - b_r \qquad\text{and}\qquad a_r > T_2 - b_r ,
--   $$
--   then there is a feasible schedule of all jobs whose length is at most
--   $$
--   \max\{T_1,\ a_r + b_r\}.
--   $$
--
--   This is case (2) of the survey's construction (Fig. 5.4). Since $T_1$ and $a_r + b_r$ are lower bounds on every schedule's length, the schedule is optimal.
--
--   **Formalization Note** "Length at most $L$" is `CompletesBy … L`: every operation ends by $L$. The statement asserts the length, not the exact start times of Fig. 5.4.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, case (2), Fig. 5.4

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312, case (2): if `T₁ − a_l ≥ T₂ − b_r` and `a_r > T₂ − b_r`, there is a feasible
schedule of length at most `max{T₁, a_r + b_r}` (Fig. 5.4). -/
theorem case_2_length {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (r l : Fin n) (hrl : r ≠ l)
    (hr : ∀ j ∈ setA a b, b j ≤ a r) (hl : ∀ j ∈ setB a b, a j ≤ b l)
    (h52 : T₂ b - b r ≤ T₁ a - a l) (h2 : T₂ b - b r < a r) :
    ∃ S : Schedule n, IsFeasible a b S ∧ CompletesBy a b S (max (T₁ a) (a r + b r)) := by sorry

end SchedSurvey.O2
