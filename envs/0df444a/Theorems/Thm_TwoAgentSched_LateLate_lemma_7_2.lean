-- Prove2me | Theorems.Thm_TwoAgentSched_LateLate_lemma_7_2
-- name    : TwoAgentSched.LateLate.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:36.387985+00:00
-- url     : https://prove2.me/theorems/e8eb0498-6f11-40c1-81c0-aec5513b8341
-- title:
--   Lemma 7.2 — $C(i,h,k)$ is the minimum completion time of the last early job
-- statement:
--   Number the jobs $J_1, \dots, J_n$ of both agents in EDD order, $d_1 \le d_2 \le \dots \le d_n$, and let $C(i,h,k)$ be the dynamic-programming table of §7. Fix $0 \le i \le n$ and $h, k \ge 0$.
--
--   1. If $C(i,h,k)$ is finite, then it is the minimum completion time of the last early job over all partial schedules of the job set $\{J_1,\dots,J_i\}$ with at most $h$ late $A$-jobs and at most $k$ late $B$-jobs:
--   $$C(i,h,k) = \min\Big\{ \sum_{j \in E} p_j \ :\ E \text{ a partial schedule of } \{J_1,\dots,J_i\} \text{ with at most } h \text{ late } A\text{-jobs and } k \text{ late } B\text{-jobs} \Big\},$$
--   and the minimum is attained.
--   2. If $C(i,h,k) = +\infty$, then no such partial schedule exists.
--
--   Here a partial schedule is given by its set $E$ of early jobs, processed first in EDD order with each job of $E$ completing by its due date, the other jobs of $\{J_1,\dots,J_i\}$ counting as late; $\sum_{j\in E} p_j$ is the completion time of its last early job. By Lemma 7.1 these are the schedules among which an optimal one is found. The lemma states that the recursion of §7 computes these minima, which is what makes the table usable for Theorem 7.3.
--
--   **Formalization Note** The paper's "feasible schedules for the job set $\{J_1,\dots,J_i\}$" is read as partial schedules described by their early set, as in the definition of $C(i,h,k)$ ("partial schedule … in which there are at most $h$ late $A$-jobs"). The reading over complete sequences with actual lateness is false: one $A$-job with $p = 1$, $d = 5$ and $h = 1$ has $C(1,1,0) = 0$, while every sequence of it completes the job early at time $1$. The boundary $C(0,h,k) = 0$ is the corrected one (see the table's definition).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 236, Lemma 7.2

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_DPTable

namespace TwoAgentSched.LateLate

/-- Lemma 7.2 (p. 236). Jobs are numbered in EDD order (`Monotone d`). For `i ≤ n`: if
`C(i, h, k)` is a finite value `c`, then `c` is the minimum of `∑_{j ∈ E} p_j` (the completion
time of the last early job) over the partial schedules `E` of `{J_1, …, J_i}` with at most `h`
late `A`-jobs and at most `k` late `B`-jobs, and it is attained; if `C(i, h, k) = +∞`, there is
no such partial schedule. -/
theorem lemma_7_2 {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (hd : Monotone d)
    (i h k : ℕ) (hi : i ≤ n) :
    (∀ c : ℕ, C p d ag i h k = (c : WithTop ℕ) →
      (∃ E : Finset (Fin n), IsPartialSchedule p d ag i h k E ∧ ∑ j ∈ E, p j = c) ∧
      ∀ E : Finset (Fin n), IsPartialSchedule p d ag i h k E → c ≤ ∑ j ∈ E, p j) ∧
    (C p d ag i h k = ⊤ → ∀ E : Finset (Fin n), ¬ IsPartialSchedule p d ag i h k E) := by sorry

end TwoAgentSched.LateLate
