-- Prove2me | Theorems.Thm_TwoAgentSched_no_idle
-- name    : TwoAgentSched.no_idle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:49:25.072516+00:00
-- url     : https://prove2.me/theorems/680c488d-b32a-48f4-b1b3-fe71db251a87
-- title:
--   §3: no convenience in keeping the machine idle
-- statement:
--   Let all processing times be nonnegative and let $S$ be any feasible schedule of the $n_A+n_B$ jobs (idle time allowed). Then there is a sequence $\sigma$ of all jobs such that
--   $$
--   C_j(\sigma) \le S_j + p_j \qquad \text{for every job } j .
--   $$
--   Consequently, for all cost functions $f^A_h$, $f^B_k$ nondecreasing on $[0,\infty)$ and every bound $Q$:
--
--   1. $f^A_{\max}$ of $\sigma$ is at most $f^A_{\max}$ of $S$;
--   2. if $S$ satisfies $f^B_{\max}\le Q$, so does $\sigma$.
--
--   This is why the paper only considers schedules without idle time, each job starting as soon as the previous job in the sequence is completed.
--
--   Differences from the source:
--   - reading: there is no convenience in keeping the machine idle → every feasible schedule is dominated job by job by the no-idle schedule of some sequence, so f^A_max does not increase and f^B_max ≤ Q is preserved; reason: this is what 'no convenience' asserts for regular objectives
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - generalization: each f_i(·) a nondecreasing function of the completion time → each cost function MonotoneOn [0, ∞); reason: completion times are ≥ 0, so values at negative arguments never enter; every nondecreasing function is an instance
--   - generalization: an integer Q → Q : ℝ; reason: integers are reals; nothing in the argument uses integrality
--   - encoding: job sets J^A = {J^A_1, …, J^A_{n_A}}, J^B = {J^B_1, …, J^B_{n_B}} → Job nA nB = Fin nA ⊕ Fin nB (A-jobs inl h, B-jobs inr k); reason: Lean convention; same instances
--   - encoding: a feasible schedule σ, a feasible assignment of starting times on one machine, nonpreemptive, zero release dates → Feasible p S: S j ≥ 0 and, for distinct jobs, S i + p i ≤ S j or S j + p j ≤ S i; completion times S j + p j; reason: the paper's definition written out; zero-length jobs may share a start time
--   - encoding: a sequence, each job started as soon as the previous one is completed → a duplicate-free list σ of all jobs (IsSeq) with completion times seqC p σ j = sum of p over the prefix of σ ending at j; reason: the no-idle schedule of a sequence written out
--   - encoding: f^A_max = max_h f^A_h(C^A_h) → fAmax: Finset.sup in EReal, equal to ⊥ when n_A = 0; reason: for n_A ≥ 1 it is the real maximum; the paper never treats an empty agent
--   - encoding: f^B_max ≤ Q → BOk: f^B_k(C^B_k) ≤ Q for every B-job k; reason: equivalent for n_B ≥ 1, written without a max so that n_B = 0 needs no convention (the constraint is then empty)
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §3, p. 231 ("Hence, there is no convenience in keeping the machine idle, and therefore each job is started as soon as the previous job in the sequence is completed")

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax

namespace TwoAgentSched

/-- **No idle time** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper. Res. 52(2) (2004), §3,
p. 231: "all these objective functions are regular … Hence, there is no convenience in keeping
the machine idle, and therefore each job is started as soon as the previous job in the sequence
is completed").

For nonnegative processing times and every feasible schedule `S` of the `n_A + n_B` jobs (idle
time allowed, zero-length jobs may share a start time) there is a sequence `σ` of all jobs whose
no-idle completion times are no later than those of `S`, job by job. Consequently, for every
choice of nondecreasing cost functions on `[0, ∞)`, agent A's objective `f^A_max` does not
increase and agent B's constraint `f^B_max ≤ Q` is preserved. -/
theorem no_idle {nA nB : ℕ} (p : Job nA nB → ℝ) (S : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hS : Feasible p S) :
    ∃ σ : List (Job nA nB), IsSeq σ ∧ (∀ j, seqC p σ j ≤ S j + p j) ∧
      ∀ (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ),
        (∀ h, MonotoneOn (fA h) (Set.Ici 0)) → (∀ k, MonotoneOn (fB k) (Set.Ici 0)) →
        fAmax fA (seqC p σ) ≤ fAmax fA (fun j => S j + p j) ∧
        (BOk fB Q (fun j => S j + p j) → BOk fB Q (seqC p σ)) := by sorry

end TwoAgentSched
