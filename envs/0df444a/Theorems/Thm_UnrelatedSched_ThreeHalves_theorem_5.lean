-- Prove2me | Theorems.Thm_UnrelatedSched_ThreeHalves_theorem_5
-- name    : UnrelatedSched.ThreeHalves.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:23.0757+00:00
-- url     : https://prove2.me/theorems/6fc2b1c1-20a3-4aef-8ae2-5af3fd6de38a
-- title:
--   Theorem 5 — makespan at most 2 on the reduced instance iff a 3-dimensional matching exists
-- statement:
--   The paper states: for the minimum makespan problem on unrelated parallel machines, the question of deciding if there exists a schedule with makespan at most 2 is NP-complete. Its proof establishes the following reduction, which is what is formalized.
--
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching over $A$, $B$, $C$ of size $n$, and consider the scheduling instance of Theorem 5 built from it: $m$ machines (one per triple), element jobs for the elements of $B$ and $C$, $t_j - 1$ dummy jobs of type $j$, and processing times $1$, $2$, $3$ as defined there. Then
--   $$\exists\,\sigma:\ C_{\max}(\sigma) \le 2 \quad\Longleftrightarrow\quad \text{the instance has a 3-dimensional matching.}$$
--
--   Since 3-DIMENSIONAL MATCHING is NP-complete and the construction is polynomial, deciding whether a schedule of makespan at most 2 exists is NP-hard.
--
--   **Formalization Note** Membership in NP, polynomiality of the construction and NP-completeness are not formalized; only the equivalence for every instance is.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 7, Theorem 5 (proof pp. 7–8)

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, Theorem 5, p. 7 (the reduction its
proof establishes): the scheduling instance built from the 3-dimensional matching instance `T`
has a schedule with makespan at most `2` if and only if `T` has a matching. -/
theorem theorem_5 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) ↔
      HasMatching T := by sorry

end UnrelatedSched.ThreeHalves
