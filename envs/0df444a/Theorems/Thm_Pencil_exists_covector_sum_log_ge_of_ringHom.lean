-- Prove2me | Theorems.Thm_Pencil_exists_covector_sum_log_ge_of_ringHom
-- name    : Pencil.exists_covector_sum_log_ge_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d8bf9e10-cced-59ab-a059-8f7e89a8a089
-- title:
--   Algebraic covector form of the pencil mean-value inequality
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$ and $\sigma\colon F\to\mathbb{C}$ a ring homomorphism. Let $r$ be a natural number, $v\colon \mathrm{Fin}\,r\to F$, and $i_0$ an index at which $\|\sigma(v_i)\|\le\|\sigma(v_{i_0})\|$ for every $i$. Let $T$ be a finite subset of an arbitrary type, let $w_t\in\mathbb{C}^r$ for $t\in T$ and let $n_t$ be natural numbers, and assume that for each $t\in T$ there is a pair $(p_1,p_2)$ of indices with $\sigma(v_{p_1})w_{t,p_2}-\sigma(v_{p_2})w_{t,p_1}\neq 0$. Then there exists $a\colon \mathrm{Fin}\,r\to F$ such that $\sum_i v_i a_i=0$ in $F$, $\|\sigma(a_i)\|\le r\,\|\sigma(v_{i_0})\|$ for all $i$, $\|\sigma(a_i)\|=\|\sigma(v_{i_0})\|$ for all $i\neq i_0$, and
--   $$\sum_{t\in T} n_t\log\Bigl(\sup_{(p_1,p_2)}\bigl\|\sigma(v_{p_1})w_{t,p_2}-\sigma(v_{p_2})w_{t,p_1}\bigr\|\Bigr)-\Bigl(\sum_{t\in T}n_t\Bigr)\bigl(r\log 2+1\bigr)\ \le\ \sum_{t\in T} n_t\log\Bigl\|\sum_i \sigma(a_i)\,w_{t,i}\Bigr\|,$$
--   the supremum being the indexed supremum over all pairs of indices in $\mathrm{Fin}\,r\times\mathrm{Fin}\,r$.
--
--   This is the version with algebraic coefficients of the mean-value estimate for a pencil of covectors through a point $v$: the covector $a$ annihilating $v$ is produced inside $F$ itself and measured only through the embedding $\sigma$, no absolute value on $F$ being used. It is applied on the Chow side of the proximity comparisons, where the cycles are defined over a number field and the relevant point $v$ has algebraic coordinates; it is cited by [`ModularCurve.JZero.prox_sum_chowSide`](thm.html#ModularCurve.JZero.prox_sum_chowSide).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Pencil_exists_covector_sum_log_ge_of_ringHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Pencil.exists_covector_sum_log_ge_of_ringHom {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {r : ℕ} (v : Fin r → F) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖σ (v i)‖ ≤ ‖σ (v i₀)‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1 ≠ 0) :
    ∃ a : Fin r → F, (∑ i, v i * a i = 0) ∧
      (∀ i, ‖σ (a i)‖ ≤ r * ‖σ (v i₀)‖) ∧ (∀ i, i ≠ i₀ → ‖σ (a i)‖ = ‖σ (v i₀)‖) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ i, σ (a i) * w t i‖ := by sorry
