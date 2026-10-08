-- Prove2me | Theorems.Thm_SchedSurvey_O2_two_machine_open_shop_optimal
-- name    : SchedSurvey.O2.two_machine_open_shop_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:52.072087+00:00
-- url     : https://prove2.me/theorems/f797c325-1087-4713-bcde-fc078c7b475e
-- title:
--   §5.2.1, p. 312 — O2‖Cmax: the optimal makespan is max{T₁, T₂, maxⱼ(aⱼ + bⱼ)}
-- statement:
--   Consider the two-machine open shop $O2$: $n$ jobs, job $J_j$ needing $a_j \ge 0$ time units on machine $M_1$ and $b_j \ge 0$ time units on machine $M_2$, in either order, without preemption; each machine processes at most one job at a time and each job is on at most one machine at a time. Let $T_1 = \sum_j a_j$ and $T_2 = \sum_j b_j$. Then the optimal makespan is
--   $$
--   C^*_{\max} = \max\Big\{T_1,\ T_2,\ \max_j\,(a_j + b_j)\Big\},
--   $$
--   and it is attained by a feasible schedule. Precisely: for every $T \ge 0$, there is a feasible schedule completing all operations by time $T$ if and only if
--   $$
--   T_1 \le T, \qquad T_2 \le T, \qquad a_j + b_j \le T \ \text{ for every job } j .
--   $$
--
--   This is the result of Gonzalez and Sahni (1976) in the form presented in §5.2.1 of the survey: the trivial lower bound on the makespan is always achieved. It makes $O2\|C_{\max}$ solvable in linear time and contrasts with $O3\|C_{\max}$, which the survey (p. 313) records as binary NP-hard.
--
--   **Formalization Note** The threshold form says exactly that the minimum makespan equals the maximum above and is attained (take $T$ equal to it), without a supremum or infimum over a possibly empty index set. Jobs are `Fin n`, 0-based; times are real. The case $n \le 1$, which the survey does not treat separately, is included.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "Since, in all cases, we have met this lower bound, it follows that the schedules constructed are optimal."

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312 (Gonzalez–Sahni): the optimal makespan of `O2‖Cmax` is
`max{T₁, T₂, maxⱼ(aⱼ + bⱼ)}`, and it is attained. Threshold form: for every `T ≥ 0`, some feasible
schedule completes by `T` iff `T₁ ≤ T`, `T₂ ≤ T` and `aⱼ + bⱼ ≤ T` for every job `j`. -/
theorem two_machine_open_shop_optimal {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : Schedule n, IsFeasible a b S ∧ CompletesBy a b S T) ↔
      (T₁ a ≤ T ∧ T₂ b ≤ T ∧ ∀ j, a j + b j ≤ T) := by sorry

end SchedSurvey.O2
