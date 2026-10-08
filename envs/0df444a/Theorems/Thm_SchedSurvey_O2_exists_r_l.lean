-- Prove2me | Theorems.Thm_SchedSurvey_O2_exists_r_l
-- name    : SchedSurvey.O2.exists_r_l
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:20.234454+00:00
-- url     : https://prove2.me/theorems/1a2ef269-ba76-4779-a877-5b8aa57e0a21
-- title:
--   §5.2.1, p. 312 — with n ≥ 2 there are distinct J_r, J_l with a_r ≥ max_{A} bⱼ and b_l ≥ max_{B} aⱼ
-- statement:
--   Consider the two-machine open shop with $n$ jobs and nonnegative processing times $a_j$ on $M_1$ and $b_j$ on $M_2$, and let $A = \{J_j \mid a_j \ge b_j\}$, $B = \{J_j \mid a_j < b_j\}$. If $n \ge 2$, there are two distinct jobs $J_r$ and $J_l$ such that
--   $$
--   a_r \ge \max_{J_j \in A} b_j, \qquad b_l \ge \max_{J_j \in B} a_j .
--   $$
--
--   The analysis of $O2\|C_{\max}$ in the survey begins by choosing such a pair; this statement asserts that the choice is always possible.
--
--   **Formalization Note** Each maximum is written as a bound on every member ($b_j \le a_r$ for all $J_j \in A$), which is also correct when $A$ or $B$ is empty. The hypothesis $n \ge 2$ is added: the page presupposes two distinct jobs.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 312, §5.2.1, "Now choose J_r and J_l to be any two distinct jobs …"

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

namespace SchedSurvey.O2

/-- §5.2.1, p. 312: with at least two jobs, there are two distinct jobs `r` (`J_r`) and `l`
(`J_l`) with `a_r ≥ max_{Jⱼ ∈ A} bⱼ` and `b_l ≥ max_{Jⱼ ∈ B} aⱼ`; the maxima over `A`, `B`
are written as bounds for every member, which is also correct when `A` or `B` is empty. -/
theorem exists_r_l {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hn : 2 ≤ n) :
    ∃ r l : Fin n, r ≠ l ∧ (∀ j ∈ setA a b, b j ≤ a r) ∧ (∀ j ∈ setB a b, a j ≤ b l) := by sorry

end SchedSurvey.O2
