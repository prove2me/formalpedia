-- Prove2me | Theorems.Thm_TwoAgentSched_TotalMax_theorem_5_5
-- name    : TwoAgentSched.TotalMax.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:32.988545+00:00
-- url     : https://prove2.me/theorems/4a9bae8a-1dca-4639-b56b-a416c5a49e26
-- title:
--   Theorem 5.5 (correctness) — the algorithm of Figure 1 solves 1‖ΣC^A_i : f^B_max ≤ Q
-- statement:
--   Consider the problem $1\|\sum C^A_i : f^B_{\max}\le Q$ with positive processing times and nondecreasing $B$-cost functions $f^B_k$, and the algorithm of Figure 1: building the schedule backwards, with $\tau$ the total length of the unscheduled jobs, place last any unscheduled $B$-job $J^B_k$ with $f^B_k(\tau)\le Q$ if there is one, otherwise a longest unscheduled $A$-job, and stop with "no solution exists" if neither is possible. Then:
--
--   1. if the instance is feasible, every schedule the algorithm can produce, under any tie-breaking, is optimal;
--   2. the algorithm can run to completion (some schedule of all jobs obeys its rule) if and only if the instance is feasible.
--
--   This is the correctness of the paper's algorithm for the unweighted problem.
--
--   **Formalization Note** The paper's Theorem 5.5 states that the problem can be solved in time $O(n_A\log n_A+n_B\log n_B)$; the running time is not formalized, only the correctness of the algorithm as Figure 1 and the text before Theorem 5.5 describe it. The algorithm is the property `IsFig1Seq` of a finished sequence.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Theorem 5.5 and Figure 1

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Rules

namespace TwoAgentSched.TotalMax

/-- Theorem 5.5, correctness half (Agnetis et al. 2004, §5.2, p. 234): the algorithm of
Figure 1 solves `1‖ΣC^A_i : f^B_max ≤ Q`.
1. On a feasible instance, every schedule of all jobs that the algorithm can produce (any
   tie-breaking) is optimal.
2. The algorithm runs to completion (some schedule of all jobs satisfies its rule) if and only
   if the instance is feasible.
The running time `O(n_A log n_A + n_B log n_B)` is not formalized. -/
theorem theorem_5_5 {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    (IsFeasibleInstance p fB Q →
      ∀ l : List (TwoAgentSched.MaxMax.Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l →
        IsFig1Seq p fB Q l → IsOptimal p fB Q l) ∧
    ((∃ l : List (TwoAgentSched.MaxMax.Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
        IsFig1Seq p fB Q l) ↔ IsFeasibleInstance p fB Q) := by sorry

end TwoAgentSched.TotalMax
