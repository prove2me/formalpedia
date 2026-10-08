-- Prove2me | Theorems.Thm_SchedComplexity_Tardiness_idle_time_removal
-- name    : SchedComplexity.Tardiness.idle_time_removal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:59.75421+00:00
-- url     : https://prove2.me/theorems/cb7d1091-d311-4c08-b343-823e106e76c6
-- title:
--   Theorem 4(d), proof p. 20 — removal of idle machine time
-- statement:
--   Consider a single-machine instance with jobs $1,\dots,n$, processing times $p_j$, weights $w_j$ and due dates $d_j$ (nonnegative integers, release dates $0$). Then:
--
--   1. for every processing order $\pi$, the schedule that processes the jobs in the order $\pi$ without idle time from time $0$ is feasible;
--   2. for every feasible schedule $S$ there is a processing order $\pi$ whose schedule without idle time satisfies
--   $$\sum_j w_jT_j(\pi)\;\le\;\sum_j w_jT_j(S).$$
--
--   The paper states this in the proof of Theorem 4(d): "Given a processing order $\pi$, we may assume that the jobs are scheduled without interruption from $0$ to $\sum_jp_{j1}$; any other schedule can be improved by removal of the idle machine time." It lets the proof work with processing orders only.
--
--   **Formalization Note** The statement is made for an arbitrary single-machine instance, not only the constructed one; the paper's argument does not use the construction. "Improved" is read as "not worsened". Schedules have start times in $\mathbb N$; the objective is computed in $\mathbb Z$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 20, proof of Theorem 4(d)

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Model

namespace SchedComplexity.Tardiness

/-- Idle-time removal (proof of Theorem 4(d), p. 20): for a single-machine instance with
processing times `p`, weights `w` and due dates `d`, the schedule without idle time of every
processing order is feasible, and every feasible schedule `S` is improved (not worsened) in
`Σ w_j T_j` by the schedule without idle time of some processing order. -/
theorem idle_time_removal {n : ℕ} (p w d : Fin n → ℕ) :
    (∀ π : Equiv.Perm (Fin n), IsFeasible p (noIdleStart p π)) ∧
    ∀ S : Fin n → ℕ, IsFeasible p S →
      ∃ π : Equiv.Perm (Fin n), orderTWT p w d π ≤ totalWeightedTardiness p w d S := by sorry

end SchedComplexity.Tardiness
