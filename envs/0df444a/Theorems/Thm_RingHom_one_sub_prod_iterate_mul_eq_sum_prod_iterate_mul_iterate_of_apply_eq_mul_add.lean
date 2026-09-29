-- Prove2me | Theorems.Thm_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
-- name    : RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c4d7bc65-d5ea-5e93-a261-5e019d5237f5
-- title:
--   Twisted geometric series for a finite-order ring endomorphism
-- statement:
--   Let $R$ be a commutative ring, let $s \colon R \to R$ be a ring homomorphism and let $\ell$ be a natural number such that the $\ell$-fold iterate of $s$ is the identity on $R$, i.e. $s^{\ell}(r) = r$ for every $r \in R$. Let $x$, $\lambda$ and $u$ be elements of $R$ satisfying the twisted relation $s(x) = \lambda x + u$. Then
--   $$\Bigl(1 - \prod_{i < \ell} s^{i}(\lambda)\Bigr)\, x \;=\; \sum_{j < \ell} \Bigl(\prod_{j < i < \ell} s^{i}(\lambda)\Bigr)\, s^{j}(u),$$
--   where the product on the left runs over $i$ in $\{0,\dots,\ell-1\}$, the inner product on the right runs over $i$ in the half-open interval from $j+1$ to $\ell$, and $s^{i}$ denotes the $i$-fold iterate of $s$ as a function. Thus $x$ is determined by $u$ and the iterates of $\lambda$ as soon as the element $1 - \prod_{i<\ell} s^{i}(\lambda)$ is invertible, or more generally a non-zero-divisor; no hypothesis of surjectivity, injectivity or order exactly $\ell$ is imposed on $s$ beyond $s^{\ell} = \mathrm{id}$.
--
--   A purely algebraic inversion statement for the twisted operator $x \mapsto s(x) - \lambda x$ attached to a ring endomorphism of finite order: the "norm" element $\prod_{i<\ell} s^i(\lambda)$ is the obstruction to solving for $x$. It is used in the proof of the adelic height bound [`AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero`](thm.html#AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero), where $s$ is a Galois-type automorphism and the non-vanishing of $1 - \prod_i s^i(\lambda)$ supplies the needed control on $x$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
    (R : Type*) [CommRing R] (s : R →+* R) (ℓ : ℕ) (hs : ∀ r : R, (⇑s)^[ℓ] r = r)
    (x lam u : R) (h : s x = lam * x + u) :
    (1 - ∏ i ∈ Finset.range ℓ, (⇑s)^[i] lam) * x =
      ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑s)^[i] lam) * (⇑s)^[j] u := by sorry
