-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_partial_schedule_valid
-- name    : SchedSurvey.OPmtn.partial_schedule_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:18.845979+00:00
-- url     : https://prove2.me/theorems/645386c7-5c5b-488f-ba80-a518571e468e
-- title:
--   §5.2.2, p. 313 — the partial schedule: Mᵢ processes Jⱼ for min{p_ij, δ} units, no machine or job twice
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $S$ be a decrementing set of $P$ (for its largest line sum $C$), $\delta>0$ and $t_0$ a time. The partial schedule of $S$ started at $t_0$ has, for each $p_{ij}\in S$, one piece in which machine $M_i$ processes job $J_j$ during
--
--   $$[\,t_0,\ t_0+\min\{p_{ij},\delta\}\,).$$
--
--   Then: no two pieces of the partial schedule share a machine or a job; every piece comes from an element of $S$, starts at $t_0$, has strictly positive length and ends by $t_0+\delta$; and for each $p_{ij}\in S$ exactly one piece has machine $M_i$ and job $J_j$. In particular the partial schedule respects both disjointness requirements of the open shop.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "Then the partial schedule constructed is such that …"

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: the partial schedule of a decrementing set is a valid schedule fragment:
for each `p_ij ∈ S` exactly one piece has machine `Mᵢ` and job `Jⱼ`, and in it `Mᵢ` processes
`Jⱼ` for `min{p_ij, δ}` units of time starting at `t₀`; every piece comes from `S`; no two
pieces share a machine or a job; and each piece has positive length at most `δ`. -/
theorem partial_schedule_valid {m n : ℕ} (P : Fin m → Fin n → ℝ) (C : ℝ)
    (S : Finset (Fin m × Fin n)) (hS : IsDecrementingSet P C S) (δ : ℝ) (hδ : 0 < δ)
    (t₀ : ℝ) :
    (partialSchedule P S δ t₀).Pairwise (fun q q' => q.mach ≠ q'.mach ∧ q.job ≠ q'.job) ∧
    (∀ q ∈ partialSchedule P S δ t₀, (q.mach, q.job) ∈ S ∧ q.start = t₀ ∧
      q.stop = t₀ + min (P q.mach q.job) δ ∧ t₀ < q.stop ∧ q.stop ≤ t₀ + δ) ∧
    (∀ x ∈ S, ((partialSchedule P S δ t₀).filter
      (fun q => decide (q.mach = x.1 ∧ q.job = x.2))).length = 1) := by sorry

end SchedSurvey.OPmtn
