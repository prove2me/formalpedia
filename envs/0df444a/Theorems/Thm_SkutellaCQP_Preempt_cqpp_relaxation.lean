-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_cqpp_relaxation
-- name    : SkutellaCQP.Preempt.cqpp_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:08.516279+00:00
-- url     : https://prove2.me/theorems/4593d75a-d340-4016-8330-a88cc6c2f2fc
-- title:
--   p. 22 — (CQP′_p) is a relaxation: the fractions of every preemptive schedule, with Z = ∑ⱼ wⱼCⱼ, are feasible
-- statement:
--   Consider an instance of $R\mid r_{ij},\,pmtn\mid\sum w_jC_j$ ($w_j\ge0$, $p_{ij}>0$, $r_{ij}\ge0$). For every feasible preemptive schedule with completion times $C_j$, the slot fractions $a_{i_kj}$ of the schedule together with $Z=\sum_j w_jC_j$ form a feasible solution of the convex quadratic program $(CQP'_p)$:
--   $$
--   \begin{aligned}
--   &\textstyle\sum_{i,k}a_{i_kj}=1\ \ \forall j,\qquad \sum_j a_{i_kj}p_{ij}\le\rho_{i_{k+1}}-\rho_{i_k}\ \ \forall i,k,\qquad a_{i_kj}=0\ \text{if}\ \rho_{i_k}<r_{ij},\qquad a\ge0,\\
--   &Z\ge b^Ta+\tfrac12a^T(D+\mathrm{diag}(c))a,\qquad Z\ge c^Ta.
--   \end{aligned}
--   $$
--   Hence the optimal value of $(CQP'_p)$ is a lower bound on the value of every preemptive schedule; this is the sentence "As a result of Lemma 4.2 the following convex quadratic program … is a relaxation of the preemptive problem" of p. 22.
--
--   **Formalization Note** The constraint $a_{i_kj}=0$ if $\rho_{i_k}<r_{ij}$ (constraint (18) of §3) is part of $(CQP'_p)$ here although the display on p. 22 omits it; Lemma 4.3 needs it, and this theorem shows it costs nothing. The capacity constraint is imposed only for slots with a successor, since $\rho_{i_{n+1}}=\infty$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), §4, p. 22, the program (CQP′_p) with (26), (27), and its introducing sentence

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

theorem cqpp_relaxation {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (P : PSched m n) (hP : PFeasible p r P) :
    CQPpFeasible p w r (frac p r P) (pval w P) := by sorry

end SkutellaCQP.Preempt
