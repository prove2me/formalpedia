-- Prove2me | Theorems.Thm_SchedSurvey_O2_symmetric_case
-- name    : SchedSurvey.O2.symmetric_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:41.012426+00:00
-- url     : https://prove2.me/theorems/92383cc7-5c10-4395-b5a1-65d6ef200563
-- title:
--   §5.2.1, p. 312 — the symmetric case T₁ − a_l < T₂ − b_r: some feasible schedule has length ≤ max{T₁, T₂, a_l + b_l}
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, $T_1 = \sum_j a_j$, $T_2 = \sum_j b_j$, the sets $A = \{J_j \mid a_j \ge b_j\}$ and $B = \{J_j \mid a_j < b_j\}$, and two distinct jobs $J_r$, $J_l$ with $a_r \ge \max_{J_j \in A} b_j$ and $b_l \ge \max_{J_j \in B} a_j$. If
--   $$
--   T_1 - a_l < T_2 - b_r ,
--   $$
--   then there is a feasible schedule of all jobs whose length is at most
--   $$
--   \max\{T_1,\ T_2,\ a_l + b_l\}.
--   $$
--
--   The survey treats this case as symmetric to the case $T_1 - a_l \ge T_2 - b_r$: exchanging the roles of the machines and of $J_r$, $J_l$, the two subcases give schedules of length $\max\{T_1, T_2\}$ and $\max\{T_2, a_l + b_l\}$; the statement combines them. Each of these values is a lower bound on every schedule's length.
--
--   **Formalization Note** The statement is not obtained by applying the cases (1)–(2) to the swapped instance: a job with $a_j = b_j$ lies in $A$ both before and after the machines are exchanged, so $A$ and $B$ do not simply trade places. The combined bound is what the optimality argument needs.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "(the case T₁ − a_l < T₂ − b_r being symmetric)"

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312, the symmetric case `T₁ − a_l < T₂ − b_r`: there is a feasible schedule of length
at most `max{T₁, T₂, a_l + b_l}` (the mirror images of cases (1) and (2) give `max{T₁, T₂}` and
`max{T₂, a_l + b_l}`). -/
theorem symmetric_case {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (r l : Fin n) (hrl : r ≠ l)
    (hr : ∀ j ∈ setA a b, b j ≤ a r) (hl : ∀ j ∈ setB a b, a j ≤ b l)
    (hsym : T₁ a - a l < T₂ b - b r) :
    ∃ S : Schedule n, IsFeasible a b S ∧
      CompletesBy a b S (max (max (T₁ a) (T₂ b)) (a l + b l)) := by sorry

end SchedSurvey.O2
