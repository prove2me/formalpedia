-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_lemma_4_2
-- name    : SkutellaCQP.Preempt.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:03.753044+00:00
-- url     : https://prove2.me/theorems/ead6037d-9043-4c89-9d86-7ad032d3d335
-- title:
--   Lemma 4.2, p. 21 — every preemptive schedule satisfies (23) and (24)
-- statement:
--   Consider an instance of $R\mid r_{ij},\,pmtn\mid\sum w_jC_j$: jobs $j$ with weights $w_j\ge0$, processing times $p_{ij}>0$ and release dates $r_{ij}\ge0$ on unrelated machines $i$, with time slots $[\rho_{i_k},\rho_{i_{k+1}})$ on each machine. Let $S$ be an arbitrary feasible preemptive schedule with completion times $C_j$, and let $a_{i_kj}$ be the fraction of job $j$ processed on machine $i$ within $[\rho_{i_k},\rho_{i_{k+1}})$. Then
--   $$
--   \sum_j w_jC_j\ \ge\ \sum_j w_j\sum_{i,k}a_{i_kj}\Bigl(\rho_{i_k}+\frac{a_{i_kj}}{2}p_{ij}+\sum_{j'\prec_i j}a_{i_kj'}p_{ij'}\Bigr)\qquad(23)
--   $$
--   and
--   $$
--   \sum_j w_jC_j\ \ge\ \sum_j w_j\sum_{i,k}a_{i_kj}\,p_{ij}.\qquad(24)
--   $$
--   Here $\prec_i$ is Smith's order on machine $i$.
--
--   The right-hand sides of (23) and (24) are those of constraints (26) and (27) of the convex quadratic program $(CQP'_p)$, which is why that program is a relaxation of the preemptive problem. The coefficient $a_{i_kj}/2$ in (23), instead of $(1+a_{i_kj})/2$ in the nonpreemptive relaxation (19), is what makes this relaxation weaker and the resulting guarantee $3$ instead of $2$.
--
--   **Formalization Note** All objects are those of `SkutellaCQP.Preempt.Setting`; the two bounds are stated as one conjunction, as in the lemma.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 21, Lemma 4.2, displays (23) and (24)

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

open Finset

theorem lemma_4_2 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (P : PSched m n) (hP : PFeasible p r P) :
    rhs23 p w r (frac p r P) ≤ pval w P ∧ rhs24 p w (frac p r P) ≤ pval w P := by sorry

end SkutellaCQP.Preempt
