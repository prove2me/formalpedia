-- Prove2me | Theorems.Thm_TwoAgentSched_seqC_feasible
-- name    : TwoAgentSched.seqC_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:48:48.860985+00:00
-- url     : https://prove2.me/theorems/082b386a-9b28-4028-a0ef-41b4b1515620
-- title:
--   A sequence processed without idle time is a feasible schedule
-- statement:
--   Let $\sigma$ be a sequence of all jobs and let all processing times be nonnegative. Starting each job when its predecessor in $\sigma$ completes, i.e. at
--   $$
--   S_j = C_j(\sigma) - p_j = \sum_{i \prec_\sigma j} p_i ,
--   $$
--   gives a feasible schedule: all start times are nonnegative and no two jobs overlap. Its completion times are the no-idle completion times $C_j(\sigma)$.
--
--   This lemma connects the sequences returned by the algorithms with the start-time schedules of the problem definition.
--
--   Differences from the source:
--   - generalization: the n_A + n_B jobs of the two agents → any job type ι; reason: the job type Fin nA ⊕ Fin nB is an instance
--   - generalization: processing times p^A_h, p^B_k of jobs (positive in scheduling practice) → real p ≥ 0 for every job; reason: zero-length jobs are allowed; every instance with positive processing times is an instance
--   - encoding: a sequence, each job started as soon as the previous one is completed → a duplicate-free list σ of all jobs (IsSeq) with completion times seqC p σ j = sum of p over the prefix of σ ending at j; reason: the no-idle schedule of a sequence written out
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §3, p. 231 ("each job is started as soon as the previous job in the sequence is completed")

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible

namespace TwoAgentSched

/-- **A sequence processed without idle time is a feasible schedule.** Agnetis–Mirchandani–
Pacciarelli–Pacifici, Oper. Res. 52(2) (2004), §3, p. 231: "each job is started as soon as the
previous job in the sequence is completed". For nonnegative processing times `p` and a sequence
`σ` of all jobs, the start times `S j = seqC p σ j − p j` (the total processing time of the jobs
before `j` in `σ`) form a feasible schedule, whose completion times are `seqC p σ`. -/
theorem seqC_feasible {ι : Type} [DecidableEq ι] (p : ι → ℝ) (σ : List ι)
    (hp : ∀ j, 0 ≤ p j) (hσ : IsSeq σ) :
    Feasible p (fun j => seqC p σ j - p j) := by sorry

end TwoAgentSched
