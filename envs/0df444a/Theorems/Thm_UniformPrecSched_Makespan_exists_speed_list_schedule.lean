-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_exists_speed_list_schedule
-- name    : UniformPrecSched.Makespan.exists_speed_list_schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:30.677985+00:00
-- url     : https://prove2.me/theorems/196db26a-16ed-4f55-a4bb-30a3074f31c3
-- title:
--   §2, p. 4 — the speed-based list scheduling algorithm produces a feasible schedule
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$ and let $k(j)$, $j = 1,\dots,n$, be any job assignment to the speed classes $\bar s_1 > \cdots > \bar s_K$. Then there is a feasible schedule of $I$ that is a speed-based list schedule for $k$: every job $j$ runs on a machine of speed $\bar s_{k(j)}$, and no machine of speed $\bar s_{k(j)}$ is idle at a time $t \ge 0$ at which all predecessors of $j$ have been completed but $j$ has not yet started.
--
--   This guarantees that every statement about the schedules produced by the speed-based list scheduling algorithm (Theorem 2.1, Theorem 3.5, Corollary 3.6, Theorem 3.7) concerns a nonempty class of schedules.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 4, §2 ("The speed-based list scheduling algorithm clearly produces a feasible schedule.")

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model

namespace UniformPrecSched.Makespan

/-- §2, p. 4: the speed-based list scheduling algorithm produces a feasible schedule, for every
job assignment `k`. -/
theorem exists_speed_list_schedule {n m : ℕ} (I : Instance n m) (k : Assignment I) :
    ∃ σ : Schedule I, IsSpeedListSchedule I k σ := by sorry

end UniformPrecSched.Makespan
