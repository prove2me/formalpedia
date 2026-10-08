-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_lemma_4_2_24
-- name    : SkutellaCQP.Preempt.lemma_4_2_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:54.335871+00:00
-- url     : https://prove2.me/theorems/4b37eeee-55eb-4b57-97c9-ad976ee8c491
-- title:
--   (24), Lemma 4.2, p. 21 — ∑ⱼ wⱼCⱼ ≥ ∑ⱼ wⱼ ∑_{i,k} a_{i_k j} p_ij for every preemptive schedule
-- statement:
--   Consider an instance of $R\mid r_{ij},\,pmtn\mid\sum w_jC_j$: jobs $j$ with weights $w_j\ge0$, processing times $p_{ij}>0$ and release dates $r_{ij}\ge0$ on unrelated machines $i$. Let $S$ be a feasible preemptive schedule with completion times $C_j$, and let $a_{i_kj}$ be the fraction of job $j$ processed on machine $i$ within the time slot $[\rho_{i_k},\rho_{i_{k+1}})$. Then
--   $$
--   \sum_j w_jC_j\ \ge\ \sum_j w_j\sum_{i,k}a_{i_kj}\,p_{ij}.
--   $$
--
--   This is the second bound (24) of Lemma 4.2. The right-hand side is the weighted sum of the processing times spent on each job in the schedule; it is the right-hand side of constraint (27) of the relaxation $(CQP'_p)$.
--
--   **Formalization Note** The schedule, the fractions $a_{i_kj}$ and $\rho$ are those of `SkutellaCQP.Preempt.Setting`. Feasibility includes that a job is never processed on two machines at once; this bound needs it.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 21, Lemma 4.2, display (24)

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

open Finset

theorem lemma_4_2_24 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (P : PSched m n) (hP : PFeasible p r P) :
    rhs24 p w (frac p r P) ≤ pval w P := by sorry

end SkutellaCQP.Preempt
