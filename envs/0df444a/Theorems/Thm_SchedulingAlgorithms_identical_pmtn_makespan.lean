-- Prove2me | Theorems.Thm_SchedulingAlgorithms_identical_pmtn_makespan
-- name    : SchedulingAlgorithms.identical_pmtn_makespan
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:13:08.82848+00:00
-- url     : https://prove2.me/theorems/e3744b66-eafa-465f-81d5-aacbb5b722af
-- title:
--   P | pmtn | Cmax — the bound LB = max{max_i p_i, (sum_i p_i)/m} is attained
-- statement:
--   Consider $n\ge 1$ jobs with positive processing times $p_1,\dots,p_n$ to be processed
--   preemptively on $m\ge 1$ identical machines (all speeds equal to $1$). Let
--
--   $$
--   LB \;:=\; \max\Bigl\{\max_i p_i,\ \frac{1}{m}\sum_{i=1}^{n}p_i\Bigr\} .
--   $$
--
--   Then (i) every feasible preemptive schedule has makespan at least $LB$, and (ii) some feasible
--   preemptive schedule has makespan exactly $LB$. In other words, $LB$ is the optimal value of
--   $P\mid pmtn\mid C_{\max}$.
--
--   Part (i) is the sentence "A lower bound for this problem is LB" on p. 108: no job can finish
--   before its own processing time has elapsed, and the total work cannot exceed $m$ times the
--   makespan. Part (ii) is the construction on the same page, McNaughton's wrap-around rule: fill
--   the machines one after another with the jobs in any order, cutting a job in two whenever the
--   current machine reaches time $LB$ and continuing the remainder on the next machine from time
--   $0$. Because $p_i\le LB$, the two parts of a cut job never overlap in time, which is what makes
--   the resulting schedule feasible.
--
--   **Formalization Note** A feasible schedule is a finite list of pieces on which no machine and
--   no job is double-booked and every job receives its full processing time; the makespan is the
--   largest stop time. No sorting of the jobs is assumed, since the rule works for any order. The
--   hypothesis $n\ge 1$ is needed for $\max_i p_i$ to be defined and is what the definition of $LB$
--   takes as an argument; $m\ge 1$ is the book's standing assumption that there are machines at all.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — Section 5.1.1, printed p. 108 (PDF p. 120), "P | pmtn | Cmax": "A lower bound for this problem is LB := max{max_i p_i, (sum_{i=1}^n p_i)/m}. A schedule meeting this bound can be constructed in O(n) time: fill the machines successively, scheduling the jobs in any order and splitting jobs into two parts whenever the above time bound is met. Schedule the second part of a preempted job on the next machine at zero time."

import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem identical_pmtn_makespan {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    (∀ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S →
        mcNaughtonBound hn p m ≤ makespan S) ∧
      ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧
        makespan S = mcNaughtonBound hn p m := by sorry
end SchedulingAlgorithms
