-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_preemptive_open_shop_optimal
-- name    : SchedSurvey.OPmtn.preemptive_open_shop_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:21.388753+00:00
-- url     : https://prove2.me/theorems/69ef8a07-6e28-4bae-9eac-9b99daa141f6
-- title:
--   §5.2.2, p. 313 — O|pmtn|Cmax: the optimal makespan is C = max{maxⱼ Σᵢ p_ij, maxᵢ Σⱼ p_ij}
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. For every time $T\ge 0$, there is a feasible preemptive schedule in which every operation is finished by time $T$ if and only if every machine load and every job length is at most $T$:
--
--   $$\big(\exists\ \text{feasible } \sigma:\ C_{\max}(\sigma)\le T\big)\iff \Big(\sum_j p_{ij}\le T\ \ \forall i\quad\text{and}\quad \sum_i p_{ij}\le T\ \ \forall j\Big).$$
--
--   Taking $T=C=\max\{\max_j\sum_i p_{ij},\max_i\sum_j p_{ij}\}$ shows that the optimal makespan is $C^*_{\max}=C$ and that it is attained. This is the theorem of Gonzalez and Sahni (1976) quoted in §5.2.2 of the survey: preemptive open-shop makespan minimization reduces to computing the largest machine load and the largest job length. The survey also uses it in §4.4.6.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. "The optimum is $C$" is stated in threshold form, which needs no maximum over a possibly empty index set and also asserts attainment. A feasible schedule is a finite list of pieces; each machine runs one job at a time, each job runs on one machine at a time, and operation $O_{ij}$ gets exactly $p_{ij}$ units on $M_i$, possibly split into several pieces. Times are real numbers. The hypothesis $T\ge 0$ matters only for $P=0$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "We clearly have C*max ≥ C. It is possible to construct a feasible schedule for which Cmax = C. Hence this schedule will be optimal."

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: "We clearly have C*max ≥ C. It is possible to construct a feasible schedule
for which Cmax = C." For `O|pmtn|Cmax` with nonnegative processing times `P` (rows = machines,
columns = jobs) and any `T ≥ 0`, a feasible preemptive schedule completing by `T` exists if and
only if every machine load `Σⱼ p_ij` and every job length `Σᵢ p_ij` is at most `T`; i.e. the
optimal makespan is `C = max{maxⱼ Σᵢ p_ij, maxᵢ Σⱼ p_ij}`, and it is attained. -/
theorem preemptive_open_shop_optimal {m n : ℕ} (P : Fin m → Fin n → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : List (Piece m n), IsFeasible P S ∧ CompletesBy S T) ↔
      ((∀ i, rowSum P i ≤ T) ∧ ∀ j, colSum P j ≤ T) := by sorry

end SchedSurvey.OPmtn
