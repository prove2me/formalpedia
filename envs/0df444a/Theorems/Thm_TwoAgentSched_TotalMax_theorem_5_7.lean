-- Prove2me | Theorems.Thm_TwoAgentSched_TotalMax_theorem_5_7
-- name    : TwoAgentSched.TotalMax.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:41.627662+00:00
-- url     : https://prove2.me/theorems/04595aee-2f9d-4ace-95e6-8f8060779941
-- title:
--   Theorem 5.7 — the least-cost backward rule yields an optimal, nondominated schedule
-- statement:
--   Consider a feasible instance of $1\|\sum C^A_i : f^B_{\max}\le Q$ with at least one $B$-job, positive processing times and nondecreasing $B$-cost functions $f^B_k$. Let $\tilde\sigma$ be any schedule produced by the modified algorithm of §5.2.1: building the schedule backwards, with $\bar\tau$ the total length of the unscheduled jobs, if some unscheduled $B$-job $J^B_k$ has $f^B_k(\bar\tau)\le Q$ then place last a $B$-job $J^B_l$ with
--   $$f^B_l(\bar\tau)=\min_{k\in U^B}f^B_k(\bar\tau)$$
--   ($U^B$ the unscheduled $B$-jobs, ties broken arbitrarily), and otherwise a longest unscheduled $A$-job. Then
--
--   1. $\tilde\sigma$ is optimal for $1\|\sum C^A_i : f^B_{\max}\le Q$, and
--   2. $\tilde\sigma$ is **nondominated**: no schedule $\bar\sigma$ has $\sum C^A_h(\bar\sigma)\le\sum C^A_h(\tilde\sigma)$ and $f^B_{\max}(\bar\sigma)\le f^B_{\max}(\tilde\sigma)$ with at least one inequality strict.
--
--   Part 2 is the printed Theorem 5.7; part 1 is the paper's description of $\tilde\sigma$ as "the optimal schedule generated in this way", which rests on Theorem 5.5. Together they say that agent $A$'s optimum under the bound $Q$ can be achieved without needlessly raising agent $B$'s cost.
--
--   **Formalization Note** The modified algorithm is the property `IsLeastCostSeq` of a finished sequence; ties are quantified universally. Dominating schedules range over all schedules of the jobs, not only those feasible for $Q$. The running time of Theorem 5.8 is not formalized.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 235, §5.2.1, the modified algorithm and Theorem 5.7

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Rules

namespace TwoAgentSched.TotalMax

/-- Theorem 5.7 (Agnetis et al. 2004, §5.2.1, p. 235), with the optimality taken from
Theorem 5.5. On a feasible instance of `1‖ΣC^A_i : f^B_max ≤ Q` with at least one B-job, every
schedule `σ̃` of all jobs produced by the modified algorithm of §5.2.1 (any tie-breaking) is
(a) optimal for `1‖ΣC^A_i : f^B_max ≤ Q`, and (b) nondominated for `(ΣC^A_i, f^B_max)`. -/
theorem theorem_5_7 {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q) (σtilde : List (TwoAgentSched.MaxMax.Job nA nB))
    (hsched : MooreLateJobs.Shared.IsSchedule Finset.univ σtilde)
    (hrule : IsLeastCostSeq p fB Q σtilde) :
    IsOptimal p fB Q σtilde ∧ IsNondominated hB p fB σtilde := by sorry

end TwoAgentSched.TotalMax
