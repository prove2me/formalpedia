-- Prove2me | Theorems.Thm_Pencil_exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge
-- name    : Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/01c1cc31-5d7c-5c76-b9a9-983dffc328ff
-- title:
--   Root-of-unity covector through v, large on a weighted family
-- statement:
--   Let $r$ be a natural number, let $v : \mathrm{Fin}\,r \to \mathbb{C}$, and let $i_0$ be an index at which the norm is maximal, i.e. $\|v_i\| \le \|v_{i_0}\|$ for every $i$. Let $\iota$ be a type, $T$ a finite subset of $\iota$, $w : \iota \to (\mathrm{Fin}\,r \to \mathbb{C})$ a family of vectors and $n : \iota \to \mathbb{N}$ a family of weights, and assume that for each $t \in T$ some $2\times 2$ minor of the pair $(v, w_t)$ is non-zero: there is a pair $p = (p_1,p_2)$ of indices with $v_{p_1} w_{t,p_2} - v_{p_2} w_{t,p_1} \ne 0$. Then there exists $z : \mathrm{Fin}\,r \to \mathbb{C}$ such that (i) every coordinate $z_j$ is a root of unity, in the sense that there is $m \in \mathbb{N}$ with $0 < m$ and $z_j^m = 1$; (ii) for every $t \in T$ the value $\sum_j z_j\,(v_{i_0} w_{t,j} - v_j w_{t,i_0})$ is non-zero; and (iii) with the supremum $M_t := \bigsqcup_{p} \|v_{p_1} w_{t,p_2} - v_{p_2} w_{t,p_1}\|$ taken over all pairs $p$ of indices, $$\sum_{t \in T} n_t \log M_t - \Bigl(\sum_{t \in T} n_t\Bigr)\bigl(r \log 2 + 1\bigr) \;\le\; \sum_{t \in T} n_t \log \Bigl\| \sum_j z_j\,(v_{i_0} w_{t,j} - v_j w_{t,i_0}) \Bigr\|.$$
--
--   This is a mean-value (Crofton-type) existence statement for the pencil of linear forms annihilating $v$: among the covectors $a(z) = v_{i_0} z - (z\cdot v)e_{i_0}$ with root-of-unity coordinates $z_j$ one can be chosen whose pairing $a(z)\cdot w_t = \sum_j z_j(v_{i_0} w_{t,j} - v_j w_{t,i_0})$ is non-zero for each member of the family and, on the weighted logarithmic average, loses at most $r\log 2 + 1$ per unit weight against the largest minor of $(v,w_t)$. The proof draws on integrability and Mahler-measure bounds for multivariate polynomials on the unit torus together with the minor comparison $\|v_i w_j - v_j w_i\| \le 2\sup_l \|v_{i_0} w_l - v_l w_{i_0}\|$, and the result feeds the proximity estimate [`ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le`](thm.html#ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Pencil_exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge {r : ℕ} (v : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, v p.1 * w t p.2 - v p.2 * w t p.1 ≠ 0) :
    ∃ z : Fin r → ℂ, (∀ j, ∃ m : ℕ, 0 < m ∧ z j ^ m = 1) ∧
      (∀ t ∈ T, ∑ j, z j * (v i₀ * w t j - v j * w t i₀) ≠ 0) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖v p.1 * w t p.2 - v p.2 * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ j, z j * (v i₀ * w t j - v j * w t i₀)‖ := by sorry
