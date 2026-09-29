-- Prove2me | Theorems.Thm_Pencil_norm_minor_le_two_mul_sup_minor_row
-- name    : Pencil.norm_minor_le_two_mul_sup_minor_row
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/209cea75-aff6-5b42-973e-5ceb371bf909
-- title:
--   All 2×2 minors bounded by twice the largest row
-- statement:
--   Let $r$ be a natural number and let $v, w : \mathrm{Fin}\,r \to \mathbb{C}$ be two vectors of length $r$. Let $i_0$ be an index such that $\|v_i\| \le \|v_{i_0}\|$ for every index $i$, i.e. the modulus of $v$ attains its maximum at $i_0$. Then for all indices $i$ and $j$ the corresponding $2\times 2$ minor of the pair $(v,w)$ satisfies
--   $$\|v_i w_j - v_j w_i\| \;\le\; 2 \cdot \sup_{l} \|v_{i_0} w_l - v_l w_{i_0}\|,$$
--   the supremum on the right being the indexed supremum over $l : \mathrm{Fin}\,r$ of the norms of the minors involving the distinguished index $i_0$ (a supremum in $\mathbb{R}$ of a finite, hence bounded, family; for $r = 0$ the hypothesis on $i_0$ cannot be met). Thus the sup-norm of the family of all Plücker coordinates of $(v,w)$ is at most twice the sup-norm of the single row of them indexed by $i_0$.
--
--   This is the elementary Plücker-row estimate: the full collection of $2\times 2$ minors (Plücker coordinates) of a pair of vectors is comparable, within a factor $2$, to those minors that involve a row where $|v|$ is largest, so that quantities such as $\log\max_{i,j}|v_iw_j-v_jw_i|$ may be computed from the $r$ linear forms $w \mapsto v_{i_0}w_l - v_lw_{i_0}$ up to an additive $\log 2$. It is used in the `Pencil` existence results [`Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge`](thm.html#Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge) and [`Pencil.exists_rootOfUnity_torus_covector_sum_log_ge`](thm.html#Pencil.exists_rootOfUnity_torus_covector_sum_log_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Pencil_norm_minor_le_two_mul_sup_minor_row.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Pencil.norm_minor_le_two_mul_sup_minor_row {r : ℕ} (v w : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖) (i j : Fin r) :
    ‖v i * w j - v j * w i‖ ≤ 2 * ⨆ l, ‖v i₀ * w l - v l * w i₀‖ := by sorry
