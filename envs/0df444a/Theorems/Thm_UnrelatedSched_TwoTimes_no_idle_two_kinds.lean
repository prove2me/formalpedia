-- Prove2me | Theorems.Thm_UnrelatedSched_TwoTimes_no_idle_two_kinds
-- name    : UnrelatedSched.TwoTimes.no_idle_two_kinds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:36.706756+00:00
-- url     : https://prove2.me/theorems/caba38a7-2e48-411e-a8d5-da6ba81e4243
-- title:
--   §5, proof of Theorem 7 — a schedule with makespan $\le pq$ has no idle time, and each machine runs $q$ element jobs or $p$ dummy jobs
-- statement:
--   Let $p$ and $q$ be relatively prime natural numbers with $0<p<q$. Let $U$ be a ground set of $qn$ elements and $S_1,\dots,S_m$ subsets of $U$, and consider the scheduling instance of Theorem 7: $m$ machines, $qn$ element jobs and $p(m-n)$ dummy jobs, where an element job takes $p$ time units on a machine whose tuple contains its element and $q$ time units otherwise, and every dummy job takes $q$ time units everywhere. Let $\sigma$ be a schedule with makespan $C_{\max}(\sigma)\le pq$. Then:
--
--   1. every machine has load exactly $pq$ (there is no idle time);
--   2. every element job $u$ runs on a machine $i=\sigma(u)$ with $u\in S_i$, so it has length $p$;
--   3. every machine $i$ either processes exactly $q$ element jobs and no dummy job, or processes no element job and exactly $p$ dummy jobs:
--
--   $$\bigl|\{u:\sigma(u)=i\}\bigr|=q \ \text{ and no dummy job on } i, \qquad\text{or}\qquad \text{no element job on } i \ \text{ and } \ \bigl|\{d:\sigma(d)=i\}\bigr|=p .$$
--
--   This is the step of the hard direction of Theorem 7 that the paper attributes to the absence of idle time and "an easy number theoretic argument"; from it the $n$ machines that run element jobs give the matching.
--
--   **Formalization Note** The hypothesis $|S_i|=q$ is not needed for these conclusions and is omitted. The case $m<n$ is included: then there are no dummy jobs and (for $n\ge1$) no schedule with makespan at most $pq$ exists, so the statement holds trivially there. Loads and makespan are those of `MatousekLP.Scheduling.Schedule`, with the processing times cast to reals.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 9, §5, proof of Theorem 7 ("no schedule with makespan pq can have idle time, and it now follows from an easy number theoretic argument that each machine processes either q element jobs of length p or p dummy jobs of length q")

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- §5, proof of Theorem 7, p. 9 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987)): "no
schedule with makespan pq can have idle time, and … each machine processes either q element jobs
of length p or p dummy jobs of length q". For `0 < p < q` relatively prime and any schedule `σ`
of the instance `twoTimes p q n S` with makespan at most `p * q`:
1. every machine has load exactly `p * q`;
2. every element job runs on a machine whose tuple contains its element (so it has length `p`);
3. every machine processes either exactly `q` element jobs and no dummy job, or no element job
   and exactly `p` dummy jobs. -/
theorem no_idle_two_kinds {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (σ : Fin (q * n + p * (m - n)) → Fin m)
    (hσ : makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) :
    (∀ i : Fin m, load (fun i j => (twoTimes p q n S i j : ℝ)) σ i = (p * q : ℝ)) ∧
      (∀ u : Fin (q * n), u ∈ S (σ (elemJob p q n m u))) ∧
      (∀ i : Fin m,
        ((Finset.univ.filter (fun u => σ (elemJob p q n m u) = i)).card = q ∧
            ∀ k : Fin (p * (m - n)), σ (dummyJob p q n m k) ≠ i) ∨
          ((∀ u : Fin (q * n), σ (elemJob p q n m u) ≠ i) ∧
            (Finset.univ.filter (fun k => σ (dummyJob p q n m k) = i)).card = p)) := by sorry

end UnrelatedSched.TwoTimes
