-- Prove2me | Theorems.Thm_TwoAgentSched_MaxMax_stuck_infeasible
-- name    : TwoAgentSched.MaxMax.stuck_infeasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:43.027266+00:00
-- url     : https://prove2.me/theorems/7e629142-9ab7-4395-ab0a-a3eafe7510a9
-- title:
--   §4 — if all A-jobs are scheduled and no B-job can be scheduled last, the instance is infeasible
-- statement:
--   Let the processing times be nonnegative and every cost function $f^B_k$ nondecreasing. Suppose that, at some point of the backward algorithm of §4, the set $U$ of unscheduled jobs is nonempty and contains no A-job, and that no B-job of $U$ can be scheduled last: with
--   $$\bar\tau=\sum_{j\in U}p_j,$$
--   every B-job $J^B_k\in U$ has $f^B_k(\bar\tau)>Q$. Then the problem $1\|f^A_{\max} : f^B_{\max}\le Q$ has no feasible schedule.
--
--   This is the stopping rule of the algorithm: it justifies declaring the instance infeasible when the rule cannot place a job.
--
--   **Formalization Note** The set $U$ is an arbitrary nonempty set of B-jobs; the statement does not require $U$ to arise from a run of the algorithm, which makes it apply to every such state.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 232, §4, the algorithm paragraph, last sentence ("If, at a certain point in the algorithm, all A-jobs have been scheduled and no B-job can be scheduled last, the instance is not feasible.")

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.MaxMax

/-- §4, the stopping rule of the backward algorithm (Agnetis et al. 2004, p. 232): "If, at a
certain point in the algorithm, all A-jobs have been scheduled and no B-job can be scheduled
last, the instance is not feasible." Let `U` be a nonempty set of unscheduled jobs containing no
A-job, and `τ̄ = Σ_{j ∈ U} p_j`. If every B-job `k ∈ U` has `f^B_k(τ̄) > Q`, then
`1‖f^A_max : f^B_max ≤ Q` has no feasible schedule. -/
theorem stuck_infeasible {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (U : Finset (Job nA nB)) (hU : U.Nonempty) (hUA : ∀ h : Fin nA, Sum.inl h ∉ U)
    (hUB : ∀ k : Fin nB, Sum.inr k ∈ U → Q < fB k (∑ j ∈ U, p j)) :
    ¬ ∃ l : List (Job nA nB), IsFeasible p fB Q l := by sorry

end TwoAgentSched.MaxMax
