-- Prove2me | Theorems.Thm_SchedulingAlgorithms_identical_pmtn_weighted_completion_nonpreemptive
-- name    : SchedulingAlgorithms.identical_pmtn_weighted_completion_nonpreemptive
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:14:08.288158+00:00
-- url     : https://prove2.me/theorems/de80818b-1db9-4e94-b4fe-fdbaaba69f54
-- title:
--   Theorem 5.7 — P | pmtn | sum w_i C_i has an optimal schedule without preemption
-- statement:
--   Consider $n$ jobs with positive processing times $p_i$ and nonnegative weights $w_i$, to be
--   processed on $m\ge 1$ identical machines, preemption allowed, with the objective
--   $\sum_i w_iC_i$ where $C_i$ is the completion time of job $i$ (the stop time of its last
--   piece). Then there is a feasible schedule **without preemption** — every job processed in a
--   single uninterrupted piece on a single machine — whose objective value is at most that of
--   every feasible preemptive schedule.
--
--   This is Theorem 5.7. Its point is that allowing preemption does not lower the optimal total
--   weighted completion time on identical machines, so $P\mid pmtn\mid\sum w_iC_i$ has the same
--   optimum as $P\parallel\sum w_iC_i$; the book uses it on p. 121 to conclude that the
--   nonincreasing-weight schedule that is optimal for $P\mid p_i=1\mid\sum w_iC_i$ remains
--   optimal when preemption is allowed. The proof takes an optimal preemptive schedule with the
--   fewest preemption times and removes the preemptions at its last preemption time by
--   exchanging tails of machine schedules, without increasing the objective.
--
--   **Formalization Note** The statement asserts existence of an optimal schedule, and that it is
--   nonpreemptive, in one existential, so it is not vacuous if the optimum were not attained; that
--   an optimum exists at all is part of what is claimed. Nonnegative weights are the book's
--   standing convention for $\sum w_iC_i$ on parallel machines (a negative weight would make the
--   objective unbounded below, and no optimal schedule would exist); positive processing times
--   are its convention for jobs. The competitor class is every feasible preemptive schedule in the
--   sense of the definition file, with any finite number of pieces.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — Section 5.1.1, printed p. 121 (PDF p. 133), Theorem 5.7: "For P | pmtn | sum w_i C_i there exists an optimal schedule without preemption."

import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem identical_pmtn_weighted_completion_nonpreemptive {n m : ℕ} (hm : 0 < m)
    (p w : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ i, 0 ≤ w i) :
    ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧ Nonpreemptive S ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S' →
        totalWeightedCompletionOf w S ≤ totalWeightedCompletionOf w S' := by sorry
end SchedulingAlgorithms
