-- Prove2me | Theorems.Thm_TwoAgentSched_sketch_correct
-- name    : TwoAgentSched.sketch_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:51:14.776987+00:00
-- url     : https://prove2.me/theorems/7c0629c9-0c04-464d-8d23-ddc91767d33c
-- title:
--   §4: correctness of the sketch of Lawler's algorithm for every run
-- statement:
--   Let all processing times be nonnegative and all cost functions nondecreasing on $[0,\infty)$, and consider any run $\rho$ of the §4 sketch: at each step, with $\bar\tau$ the sum of the processing times of the unscheduled jobs, either any unscheduled B-job with $f^B_k(\bar\tau)\le Q$ is scheduled to end at $\bar\tau$, or, if there is no such B-job, an unscheduled A-job with minimum $f^A_h(\bar\tau)$ is.
--
--   1. If the run has scheduled every job, the resulting sequence satisfies $f^B_{\max}\le Q$ and its $f^A_{\max}$ is at most that of every feasible schedule satisfying $f^B_{\max}\le Q$.
--   2. If the run has scheduled every A-job, at least one B-job is unscheduled, and no unscheduled B-job has $f^B_k(\bar\tau)\le Q$, then no feasible schedule satisfies $f^B_{\max}\le Q$: "the instance is not feasible".
--
--   This is the correctness of the algorithm before its refinement by deadlines on p. 233.
--
--   Differences from the source:
--   - reading: the sketch, which may schedule any unscheduled B-job with f^B_k(τ̄) ≤ Q and any minimizing A-job → every run of the sketch (IsSketchSuffix); reason: the sketch is nondeterministic; its correctness is a statement about each of its runs
--   - reading: Lawler's algorithm for this special case → optimality for problem CP against every feasible schedule, and the infeasibility test; reason: the purpose of the sketch, stated by the reduction just before it
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
--   - encoding: job sets J^A = {J^A_1, …, J^A_{n_A}}, J^B = {J^B_1, …, J^B_{n_B}} → Job nA nB = Fin nA ⊕ Fin nB (A-jobs inl h, B-jobs inr k); reason: Lean convention; same instances
--   - encoding: a feasible schedule σ, a feasible assignment of starting times on one machine, nonpreemptive, zero release dates → Feasible p S: S j ≥ 0 and, for distinct jobs, S i + p i ≤ S j or S j + p j ≤ S i; completion times S j + p j; reason: the paper's definition written out; zero-length jobs may share a start time
--   - encoding: a sequence, each job started as soon as the previous one is completed → a duplicate-free list σ of all jobs (IsSeq) with completion times seqC p σ j = sum of p over the prefix of σ ending at j; reason: the no-idle schedule of a sequence written out
--   - encoding: f^A_max = max_h f^A_h(C^A_h) → fAmax: Finset.sup in EReal, equal to ⊥ when n_A = 0; reason: for n_A ≥ 1 it is the real maximum; the paper never treats an empty agent
--   - encoding: f^B_max ≤ Q → BOk: f^B_k(C^B_k) ≤ Q for every B-job k; reason: equivalent for n_B ≥ 1, written without a max so that n_B = 0 needs no convention (the constraint is then empty)
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 ("In view of the above reduction, Lawler's algorithm for this special case may be sketched as follows. …")

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax
import Definitions.Def_TwoAgentSched_IsSketchSuffix

namespace TwoAgentSched

/-- **Correctness of the §4 sketch of Lawler's algorithm** (Agnetis–Mirchandani–Pacciarelli–
Pacifici, Oper. Res. 52(2) (2004), §4, p. 232), for every run, whatever B-job and whatever
minimizing A-job each step picks. For nonnegative processing times and cost functions
nondecreasing on `[0, ∞)`:
1. every complete run `ρ` (all jobs fixed) is a sequence satisfying `f^B_max ≤ Q` whose
   `f^A_max` is at most that of every feasible schedule satisfying `f^B_max ≤ Q`;
2. if a run has fixed every A-job, at least one B-job is unscheduled, and no unscheduled B-job
   has `f^B_k(τ̄) ≤ Q`, then no feasible schedule satisfies `f^B_max ≤ Q` ("the instance is not
   feasible"). -/
theorem sketch_correct {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (hp : ∀ j, 0 ≤ p j)
    (hfA : ∀ h, MonotoneOn (fA h) (Set.Ici 0)) (hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0)) :
    (∀ ρ, IsSketchSuffix p fA fB Q ρ → (∀ j, j ∈ ρ) →
      IsSeq ρ ∧ BOk fB Q (seqC p ρ) ∧
      ∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
        fAmax fA (seqC p ρ) ≤ fAmax fA (fun j => S j + p j)) ∧
    (∀ ρ, IsSketchSuffix p fA fB Q ρ → (∀ h, Sum.inl h ∈ ρ) → (∃ k, Sum.inr k ∉ ρ) →
      (∀ k, Sum.inr k ∉ ρ → Q < fB k (remSum p ρ)) →
      ¬ ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) := by sorry

end TwoAgentSched
