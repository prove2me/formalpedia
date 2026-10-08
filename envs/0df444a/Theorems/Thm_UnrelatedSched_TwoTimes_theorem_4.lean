-- Prove2me | Theorems.Thm_UnrelatedSched_TwoTimes_theorem_4
-- name    : UnrelatedSched.TwoTimes.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:14.388283+00:00
-- url     : https://prove2.me/theorems/a33ab285-d9de-4f9a-bec1-79190f116345
-- title:
--   Theorem 4 — a schedule with makespan at most 3 exists iff the 3-dimensional matching instance has a matching
-- statement:
--   Let $A=\{a_1,\dots,a_n\}$, $B=\{b_1,\dots,b_n\}$, $C=\{c_1,\dots,c_n\}$ be disjoint sets and $T_1,\dots,T_m$ triples with one element in each of $A$, $B$, $C$. Consider the scheduling instance on $m$ unrelated machines built from them: $3n$ element jobs, one per element of $A\cup B\cup C$, and $m-n$ dummy jobs; machine $i$ processes the element jobs of the three elements of $T_i$ in one time unit each and every other job in three time units. Then
--
--   $$\exists\ \text{schedule } \sigma \text{ with } C_{\max}(\sigma)\le 3 \iff \text{the family } \{T_1,\dots,T_m\} \text{ contains a matching},$$
--
--   where a schedule assigns every job to one machine, the load of a machine is the sum of the processing times of its jobs, and the makespan $C_{\max}$ is the largest load.
--
--   The paper states Theorem 4 as: deciding whether a schedule with makespan at most 3 exists is NP-complete. Its proof is a reduction from 3-dimensional matching, and the equivalence above is what that proof establishes; it is what is formalized. Theorem 4 is the case $\{p,q\}=\{1,3\}$ of the paper's last result, Theorem 7, which recalls it.
--
--   **Formalization Note** NP-completeness, membership in NP and the polynomial size of the reduction are not formalized. The statement holds for all $m$ and $n$: when $m<n$ there are no dummy jobs and neither side holds (when $n\ge1$), which stands in for the paper's "trivial 'no' instance".
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 7, Theorem 4 and its proof

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem4Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- Theorem 4 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), p. 7), in the form its proof
establishes: for the scheduling instance `thm4Times T` built from a 3-DIMENSIONAL MATCHING
instance `T` (`m` machines, `3n` element jobs, `m - n` dummy jobs, all processing times in
`{1, 3}`), there is a schedule with makespan at most `3` if and only if `T` has a matching.
"NP-complete" is not formalized. -/
theorem theorem_4 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (3 * n + (m - n)) → Fin m,
        makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3) ↔
      ∃ F' : Finset (Fin m), IsThreeDimMatching T F' := by sorry

end UnrelatedSched.TwoTimes
