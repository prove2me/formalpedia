-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_pseudoforest_job_matching
-- name    : UnrelatedSched.TwoApprox.pseudoforest_job_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:16:59.127687+00:00
-- url     : https://prove2.me/theorems/99b1c202-28b6-4a0c-8061-d4fab1b368f7
-- title:
--   §2, proof of Theorem 1, pp. 4–5 — in a pseudoforest, job nodes of degree ≥ 2 can be matched to machines
-- statement:
--   Let $m\ge 1$, and let $E$ be the edge set of a bipartite graph between machines $\{1,\dots,m\}$ and jobs $\{1,\dots,n\}$ which is a pseudoforest (every set $S$ of machines and $T$ of jobs spans at most $|S|+|T|$ edges). Let $T_0$ be a set of jobs each of which has degree at least $2$ in $E$. Then there is a matching that covers all of $T_0$: a map $f$ from jobs to machines with
--   $$(f(j),j)\in E\ \text{ for all } j\in T_0,\qquad f \text{ injective on } T_0 .$$
--
--   In the proof of the Rounding Theorem this is applied to the support graph of a vertex after deleting the jobs that the vertex already assigns integrally; the matching assigns each remaining job to a distinct machine.
--
--   **Formalization Note** The paper's graph $G'$ is the support graph with the job nodes of degree $1$ removed; here the jobs of $G'$ are any set $T_0$ of jobs of degree at least $2$, and the pseudoforest property of the whole graph is assumed (it passes to $G'$). The degree of job $j$ is the number of edges of $E$ at $j$.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), pp. 4–5, §2, proof of Theorem 1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- §2, proof of Theorem 1, pp. 4–5: in a machine–job pseudoforest, any set of jobs each of degree
at least 2 can be matched into the machines. -/
theorem pseudoforest_job_matching {m n : ℕ} (hm : 0 < m)
    (E : Finset (Fin m × Fin n)) (hE : IsPseudoforest E)
    (T : Finset (Fin n)) (hdeg : ∀ j ∈ T, 2 ≤ (E.filter fun e => e.2 = j).card) :
    ∃ f : Fin n → Fin m, (∀ j ∈ T, (f j, j) ∈ E) ∧ Set.InjOn f (T : Set (Fin n)) := by sorry

end UnrelatedSched.TwoApprox
