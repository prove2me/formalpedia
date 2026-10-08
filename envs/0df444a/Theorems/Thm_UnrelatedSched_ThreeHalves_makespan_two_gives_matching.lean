-- Prove2me | Theorems.Thm_UnrelatedSched_ThreeHalves_makespan_two_gives_matching
-- name    : UnrelatedSched.ThreeHalves.makespan_two_gives_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:16.545831+00:00
-- url     : https://prove2.me/theorems/6fe3a542-9a89-4af5-b55f-548db4a8ae4f
-- title:
--   Theorem 5, proof (p. 8) — a schedule of makespan at most 2 yields a 3-dimensional matching
-- statement:
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching over sets of size $n$, and consider the scheduling instance of Theorem 5 built from it. If some schedule $\sigma$ of this instance has
--   $$C_{\max}(\sigma) \le 2,$$
--   then the matching instance has a matching.
--
--   This is the "only if" half of the reduction of Theorem 5.
--
--   **Formalization Note** No assumption $t_j \ge 1$ is made: when some $a_j$ lies in no triple there is no schedule of makespan at most 2 (and no matching), so the implication holds in that case as well.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 8, Section 4, proof of Theorem 5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 8 (converse):
if the scheduling instance of Theorem 5 built from `T` has a schedule with makespan at most `2`,
then `T` has a matching. -/
theorem makespan_two_gives_matching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (σ : Fin (numJobs T) → Fin m) (hσ : makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) :
    HasMatching T := by sorry

end UnrelatedSched.ThreeHalves
