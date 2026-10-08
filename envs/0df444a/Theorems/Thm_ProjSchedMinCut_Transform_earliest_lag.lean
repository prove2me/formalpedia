-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_earliest_lag
-- name    : ProjSchedMinCut.Transform.earliest_lag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:56.457046+00:00
-- url     : https://prove2.me/theorems/bfff7766-344c-4dbd-8d07-5fcdd65e8f89
-- title:
--   Proof of Lemma 1, p. 7 — the time lags respect the earliest start times: e(i) + d_ij ≤ e(j)
-- statement:
--   Consider an instance of the project scheduling problem with start-time dependent costs: jobs $J = \{0,\dots,n\}$, processing times $p_j \ge 0$, time lags $(i,j) \in L$ of integral length $d_{ij}$, horizon $T$, and non-negative costs $w_{jt}$. Assume that a feasible schedule exists (time-feasible and within the horizon), and let $e(j)$ be the earliest feasible start time of job $j$. Then for every time lag $(i,j) \in L$,
--   $$e(i) + d_{ij} \le e(j).$$
--
--   In the proof of Lemma 1 this is the step "there is a time lag between $i$ and $j$ of length $t - s$, hence $e(i) + (t-s) \le e(j)$"; it is what rules out a temporal arc leaving the first block of a job's chain.
--
--   **Formalization Note** The cost non-negativity $w_{jt} \ge 0$ is carried for uniformity with the standing assumptions of §2, although the claim does not use it. $e(j)$ is defined as the minimum of $S_j$ over feasible schedules (see the definitions file).
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 7, proof of Lemma 1

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Proof of Lemma 1, p. 7: a time lag `(i, j) ∈ L` of length `d_ij` respects the earliest start
times, `e(i) + d_ij ≤ e(j)`. -/
theorem earliest_lag {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ ij ∈ I.L, I.earliest ij.1 + I.d ij.1 ij.2 ≤ I.earliest ij.2 := by sorry

end ProjSchedMinCut.Transform
