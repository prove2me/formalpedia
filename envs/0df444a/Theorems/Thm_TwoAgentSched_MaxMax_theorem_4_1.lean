-- Prove2me | Theorems.Thm_TwoAgentSched_MaxMax_theorem_4_1
-- name    : TwoAgentSched.MaxMax.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:43.576951+00:00
-- url     : https://prove2.me/theorems/d97632dc-a572-4e4e-aa7a-4899d11231e0
-- title:
--   Theorem 4.1 (correctness) — the backward rule solves $1\|f^A_{\max} : f^B_{\max}\le Q$
-- statement:
--   Consider $n_A\ge1$ A-jobs and $n_B$ B-jobs on one machine, with nonnegative processing times, nondecreasing cost functions $f^A_h$, $f^B_k$, and a bound $Q$. The backward rule of §4 builds a schedule from the end: with $\bar\tau$ the total processing time of the unscheduled jobs, it places last any unscheduled B-job $J^B_k$ with $f^B_k(\bar\tau)\le Q$, and if there is none, an unscheduled A-job with the smallest $f^A_h(\bar\tau)$; it stops when all A-jobs are scheduled and no B-job can be placed. Then:
--
--   1. every complete schedule the rule can produce, under any tie-breaking, is optimal for
--   $$1\|f^A_{\max} : f^B_{\max}\le Q:\quad \min\ f^A_{\max}(\sigma)\ \text{ subject to }\ f^B_{\max}(\sigma)\le Q;$$
--   2. the rule produces a complete schedule if and only if the instance has a feasible schedule.
--
--   Printed as "$1\|f^A_{\max} : f^B_{\max}$ can be solved in time $O(n_A^2+n_B\log n_B)$", this is the paper's first and simplest two-agent result: a single-machine scheduling problem between two agents with maximum-cost objectives is solved by a greedy rule.
--
--   **Formalization Note** Only the correctness of the algorithm is formalized; the running time $O(n_A^2+n_B\log n_B)$ is not. "The rule produces a complete schedule" is stated as the existence of a schedule of all jobs satisfying the backward-rule property, at every position of which the rule's choice is legal.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, Theorem 4.1, with the algorithm and its justification on pp. 232–233, §4

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_BackwardRule

namespace TwoAgentSched.MaxMax

/-- Theorem 4.1, correctness of the algorithm (Agnetis et al. 2004, §4, pp. 232–233): the
backward rule solves `1‖f^A_max : f^B_max ≤ Q`.
1. Every sequence of all `nA + nB` jobs that the backward rule can produce (any tie-breaks) is
   optimal for `1‖f^A_max : f^B_max ≤ Q`.
2. The backward rule produces a complete sequence (never stops) if and only if the instance is
   feasible.
The running time `O(n_A² + n_B log n_B)` of the printed theorem is not formalized. -/
theorem theorem_4_1 {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (hfA : ∀ h, Monotone (fA h))
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    (∀ l : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l →
      IsBackwardRuleSeq p fA fB Q l → IsOptimal hA p fA fB Q l) ∧
    ((∃ l : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
        IsBackwardRuleSeq p fA fB Q l) ↔
      ∃ l : List (Job nA nB), IsFeasible p fB Q l) := by sorry

end TwoAgentSched.MaxMax
