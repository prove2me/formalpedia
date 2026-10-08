-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_lower_bound
-- name    : SchedSurvey.OPmtn.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:50:00.993999+00:00
-- url     : https://prove2.me/theorems/b3c9dbaf-5224-4966-bcb7-bc65fa594c9f
-- title:
--   §5.2.2, p. 313 — C*max ≥ C: every machine load and job length is at most the makespan
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $\sigma$ be a feasible preemptive schedule for $P$ in which every piece ends by time $T\ge 0$. Then
--
--   $$\sum_{j} p_{ij}\le T\quad\text{for every machine } M_i,\qquad \sum_{i} p_{ij}\le T\quad\text{for every job } J_j.$$
--
--   Equivalently, $C^*_{\max}\ge C=\max\{\max_j\sum_i p_{ij},\max_i\sum_j p_{ij}\}$. This is the lower half of the optimality theorem for $O|pmtn|C_{\max}$: no machine can finish its load, and no job its total processing, faster than in the given amount of time.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. The hypothesis $T\ge 0$ is needed only for $P=0$, where the empty schedule completes by every $T$, including negative ones.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "We clearly have C*max ≥ C."

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: "We clearly have C*max ≥ C." Every feasible preemptive open-shop schedule
that completes by `T ≥ 0` has every machine load and every job length at most `T`. -/
theorem lower_bound {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (S : List (Piece m n)) (hS : IsFeasible P S) (T : ℝ) (hT : 0 ≤ T)
    (hST : CompletesBy S T) :
    (∀ i, rowSum P i ≤ T) ∧ ∀ j, colSum P j ≤ T := by sorry

end SchedSurvey.OPmtn
