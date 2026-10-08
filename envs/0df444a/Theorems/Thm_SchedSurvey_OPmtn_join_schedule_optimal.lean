-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_join_schedule_optimal
-- name    : SchedSurvey.OPmtn.join_schedule_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:43.662242+00:00
-- url     : https://prove2.me/theorems/1f8cd24d-939e-4d5d-9276-8aae1ba37837
-- title:
--   §5.2.2, p. 313 — joining the partial schedules yields a feasible schedule with Cmax ≤ C
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $C$ be its largest row or column sum. Suppose $(P_t,S_t,\delta_t)_{t<k}$ is a run of the procedure of §5.2.2 starting from $P_0=P$: for each $t<k$, $S_t$ is a decrementing set of $P_t$ with respect to $C_t=C-(\delta_0+\dots+\delta_{t-1})$, $\delta_t>0$ satisfies the constraints (1), (2), (3) for $P_t$, $C_t$, $S_t$, and $P_{t+1}$ is $P_t$ with each entry of $S_t$ replaced by $\max\{0,p-\delta_t\}$. Suppose the run ends with $P_k=0$. Join the partial schedules: stage $t$ runs, for each $p_{ij}\in S_t$, machine $M_i$ on job $J_j$ during $[\tau_t,\tau_t+\min\{p_{ij},\delta_t\})$, where $\tau_t=\delta_0+\dots+\delta_{t-1}$. Then the joined schedule is a feasible preemptive schedule for $P$, and
--
--   $$C_{\max}\le C .$$
--
--   Combined with the lower bound $C^*_{\max}\ge C$ this schedule is optimal, as the survey states.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. The step lengths need only satisfy (1)–(3), not be maximal.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "Joining together the partial schedules obtained for successive decrementing sets then yields an optimal preemptive schedule for P."

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: "Joining together the partial schedules obtained for successive
decrementing sets then yields an optimal preemptive schedule for P." If stages `t < k` run the
procedure (decrementing set `S_t` of `P_t` for `C_t = C − (δ₀ + ⋯ + δ_{t−1})`, `δ_t > 0`
satisfying (1), (2), (3), `P_{t+1} = P_t′`) from `P₀ = P` and end with `P_k = 0`, then the
joined schedule is feasible for `P` and completes by `C`. -/
theorem join_schedule_optimal {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (C : ℝ) (hC : IsMaxLoad P C) (k : ℕ) (Ps : ℕ → Fin m → Fin n → ℝ)
    (Ss : ℕ → Finset (Fin m × Fin n)) (δs : ℕ → ℝ) (h0 : Ps 0 = P)
    (hstep : ∀ t < k,
      IsDecrementingSet (Ps t) (C - ∑ s ∈ Finset.range t, δs s) (Ss t) ∧ 0 < δs t ∧
      Admissible (Ps t) (C - ∑ s ∈ Finset.range t, δs s) (Ss t) (δs t) ∧
      Ps (t + 1) = reduce (Ps t) (Ss t) (δs t))
    (hk : Ps k = 0) :
    IsFeasible P (joinSchedule Ps Ss δs k) ∧
      CompletesBy (joinSchedule Ps Ss δs k) C := by sorry

end SchedSurvey.OPmtn
