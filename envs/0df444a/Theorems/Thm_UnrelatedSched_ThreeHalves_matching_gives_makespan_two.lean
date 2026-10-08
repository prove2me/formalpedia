-- Prove2me | Theorems.Thm_UnrelatedSched_ThreeHalves_matching_gives_makespan_two
-- name    : UnrelatedSched.ThreeHalves.matching_gives_makespan_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:13.724689+00:00
-- url     : https://prove2.me/theorems/775b4434-b693-47c1-8963-f5c49ba7bced
-- title:
--   Theorem 5, proof (p. 8) — a 3-dimensional matching yields a schedule of makespan 2
-- statement:
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching over sets of size $n$, and consider the scheduling instance of Theorem 5 built from it (element jobs for $b_k$ and $c_l$, $t_j - 1$ dummy jobs of type $j$, processing times $1$, $2$, $3$). If the instance has a matching, then there is a schedule $\sigma$ with
--   $$C_{\max}(\sigma) \le 2.$$
--
--   This is the "if" half of the reduction of Theorem 5.
--
--   **Formalization Note** The makespan is the published `MatousekLP.Scheduling.makespan` applied to the real cast of the processing-time matrix `P T`; schedules are maps from the enumerated jobs to the machines.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 8, Section 4, proof of Theorem 5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 8 (first half):
if the 3-dimensional matching instance `T` has a matching, then the scheduling instance of
Theorem 5 built from `T` has a schedule with makespan at most `2`. -/
theorem matching_gives_makespan_two {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : HasMatching T) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by sorry

end UnrelatedSched.ThreeHalves
