-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_power_of_preemption
-- name    : SkutellaCQP.Preempt.power_of_preemption
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:33.063092+00:00
-- url     : https://prove2.me/theorems/dac870aa-821f-407e-a5dd-7cd51d247432
-- title:
--   Corollary 4.6, p. 23 — for R | rᵢⱼ | Σ wⱼCⱼ, an optimal nonpreemptive schedule is within factor 3 of an optimal preemptive one, within 2 without release dates
-- statement:
--   Consider $n$ jobs and $m$ unrelated parallel machines; job $j$ has weight $w_j\ge0$, and on machine $i$ processing time $p_{ij}>0$ and release date $r_{ij}\ge0$. For every feasible preemptive schedule $P$ (jobs may be interrupted and resumed later on the same or another machine, a machine processes one job at a time, a job runs on one machine at a time, nothing of job $j$ runs on machine $i$ before $r_{ij}$) there is a feasible **nonpreemptive** schedule $S$ with
--   $$
--   \sum_j w_jC_j(S)\ \le\ 3\sum_j w_jC_j(P).
--   $$
--   If moreover all release dates are $0$, there is a feasible nonpreemptive schedule $S$ with
--   $$
--   \sum_j w_jC_j(S)\ \le\ 2\sum_j w_jC_j(P).
--   $$
--
--   This is Corollary 4.6: the value of an optimal nonpreemptive schedule is at most a factor $3$ above the value of an optimal preemptive schedule, and at most a factor $2$ in the absence of nontrivial release dates. It bounds the "power of preemption" for $R\mid r_{ij}\mid\sum w_jC_j$.
--
--   **Formalization Note** The ratio of optima is stated in the equivalent form "for every preemptive schedule there is a nonpreemptive one within the factor", which needs no existence of optimal schedules. Schedules are finite lists of pieces (job, machine, start, stop); "nonpreemptive" means exactly one piece per job. Communication delays are not modelled; without them the preemptive class is the largest, so this form implies the bound under any delay model. "In the absence of nontrivial release dates" is read as $r_{ij}=0$ for all $i,j$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 23, Corollary 4.6

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

theorem power_of_preemption {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j) :
    ∀ P : PSched m n, PFeasible p r P →
      (∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 3 * pval w P) ∧
      ((∀ i j, r i j = 0) →
        ∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 2 * pval w P) := by sorry

end SkutellaCQP.Preempt
