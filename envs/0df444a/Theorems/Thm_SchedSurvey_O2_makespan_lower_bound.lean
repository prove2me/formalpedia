-- Prove2me | Theorems.Thm_SchedSurvey_O2_makespan_lower_bound
-- name    : SchedSurvey.O2.makespan_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:10.537463+00:00
-- url     : https://prove2.me/theorems/05c9568e-04fc-46b5-9b18-3f6eac4f49cd
-- title:
--   §5.2.1, p. 312 — every feasible O2 schedule has Cmax ≥ max{T₁, T₂, maxⱼ(aⱼ + bⱼ)}
-- statement:
--   Consider the two-machine open shop with nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, and let $T_1 = \sum_j a_j$, $T_2 = \sum_j b_j$. For every feasible schedule,
--   $$
--   C_{\max} \ge \max\Big\{T_1,\ T_2,\ \max_j\,(a_j + b_j)\Big\}.
--   $$
--   Equivalently: if a feasible schedule completes every operation by time $T \ge 0$, then $T_1 \le T$, $T_2 \le T$, and $a_j + b_j \le T$ for every job $j$.
--
--   The three terms are the loads of the two machines and the longest job: a machine processes one job at a time, and a job is on one machine at a time. This lower bound is what makes the survey's constructed schedules optimal.
--
--   **Formalization Note** $C_{\max} \ge X$ is stated through thresholds: every $T$ with $C_{\max} \le T$ satisfies $X \le T$. The hypothesis $T \ge 0$ matters only for $n = 0$, where $C_{\max} = 0$ and the bound reads $0 \le T$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "For any feasible schedule we obviously have that Cmax ≥ max{T₁, T₂, maxⱼ{aⱼ + bⱼ}}"

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312: every feasible schedule has `Cmax ≥ max{T₁, T₂, maxⱼ(aⱼ + bⱼ)}`, stated as: if a
feasible schedule completes by `T ≥ 0`, then `T₁ ≤ T`, `T₂ ≤ T` and `aⱼ + bⱼ ≤ T` for every job. -/
theorem makespan_lower_bound {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (S : Schedule n) (hS : IsFeasible a b S) (T : ℝ) (hT : 0 ≤ T)
    (hST : CompletesBy a b S T) :
    T₁ a ≤ T ∧ T₂ b ≤ T ∧ ∀ j, a j + b j ≤ T := by sorry

end SchedSurvey.O2
