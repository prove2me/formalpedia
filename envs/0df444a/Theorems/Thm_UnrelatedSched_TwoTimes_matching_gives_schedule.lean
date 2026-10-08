-- Prove2me | Theorems.Thm_UnrelatedSched_TwoTimes_matching_gives_schedule
-- name    : UnrelatedSched.TwoTimes.matching_gives_schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:31.714766+00:00
-- url     : https://prove2.me/theorems/31a05a0f-7de0-4da4-8f77-4b9eae779560
-- title:
--   §5, proof of Theorem 7 — each $q$-dimensional matching gives a schedule with makespan $pq$
-- statement:
--   Let $U$ be a ground set of $qn$ elements and $S_1,\dots,S_m$ subsets of $U$ with $|S_i|=q$ for every $i$. Consider the scheduling instance of Theorem 7: $m$ machines, $qn$ element jobs and $p(m-n)$ dummy jobs, where an element job takes $p$ time units on a machine whose tuple contains its element and $q$ time units otherwise, and every dummy job takes $q$ time units everywhere. If the family has a matching, that is, $n$ of the tuples whose union is $U$, then there is a schedule $\sigma$ with
--
--   $$C_{\max}(\sigma)\le pq .$$
--
--   This is the easy direction of the reduction in Theorem 7.
--
--   **Formalization Note** The statement holds for all natural numbers $p$, $q$; the standing assumptions $0<p<q$ and $\gcd(p,q)=1$ of Theorem 7 are not needed for this direction and are omitted, which makes the statement stronger. Schedules, loads and the makespan are those of `MatousekLP.Scheduling.Schedule`, with the natural-number processing times cast to reals.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), pp. 8-9, §5, proof of Theorem 7 ("It is trivial to see that for each matching there is a schedule with makespan pq.")

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- §5, proof of Theorem 7, p. 9 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987)): "for each
matching there is a schedule with makespan pq". If the family `S` of `q`-subsets of the ground set
`Fin (q * n)` has a matching `F'`, the scheduling instance `twoTimes p q n S` has a schedule whose
makespan is at most `p * q`. -/
theorem matching_gives_schedule (p q : ℕ) {m n : ℕ} (S : Fin m → Finset (Fin (q * n)))
    (hS : ∀ i, (S i).card = q) (F' : Finset (Fin m)) (hF' : IsQMatching S F') :
    ∃ σ : Fin (q * n + p * (m - n)) → Fin m,
      makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ) := by sorry

end UnrelatedSched.TwoTimes
