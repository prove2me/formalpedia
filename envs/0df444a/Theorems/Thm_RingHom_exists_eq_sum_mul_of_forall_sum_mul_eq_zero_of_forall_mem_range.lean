-- Prove2me | Theorems.Thm_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range
-- name    : RingHom.exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/5b184c8a-fd83-5222-914f-97fdddbea065
-- title:
--   Linear relations over K among φ(k)-valued functions descend to k
-- statement:
--   Let $k$ and $K$ be fields and $\varphi : k \to K$ a ring homomorphism, let $X$ be any type and $n$ a natural number. Let $f : \mathrm{Fin}\,n \to X \to K$ be a family of $n$ functions on $X$ with values in $K$, and assume every value $f_i(x)$ lies in the range of $\varphi$. Let $c : \mathrm{Fin}\,n \to K$ be coefficients satisfying the relation $\sum_{i} c_i\, f_i(x) = 0$ for every $x \in X$. The conclusion asserts the existence of a natural number $m$, a family $d : \mathrm{Fin}\,m \to K$ of scalars and a family $v : \mathrm{Fin}\,m \to \mathrm{Fin}\,n \to k$ of vectors with entries in $k$ such that, first, each $v_j$ is itself a relation among the $f_i$, i.e. $\sum_i \varphi(v_{j,i})\, f_i(x) = 0$ for all $j$ and all $x \in X$, and second, the original coefficients are $K$-linear combinations of these, $c_i = \sum_j d_j\, \varphi(v_{j,i})$ for every $i$. No finiteness or separability assumption on the extension $\varphi$ is imposed, and $X$ may be infinite.
--
--   This is the statement that the space of $K$-solutions of a homogeneous linear system whose coefficients lie in $\varphi(k)$ is spanned over $K$ by its $k$-rational solutions, a form of linear disjointness obtained from the flatness of base change along $\varphi$. It is used in the treatment of $q$-expansions on modular curves, where relations over a residue field among reductions of modular functions with coefficients in a smaller field have to be traced back to that smaller field; it is cited by [`ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero`](thm.html#ModularCurve.FullLevel.sum_algebraMap_mul_apply_eq_zero_of_sum_smul_residue_eq_zero) and its variant for primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.exists_eq_sum_mul_of_forall_sum_mul_eq_zero_of_forall_mem_range
    {k K : Type*} [Field k] [Field K] (φ : k →+* K) {X : Type*} {n : ℕ}
    (f : Fin n → X → K) (hf : ∀ i x, f i x ∈ Set.range φ)
    (c : Fin n → K) (hc : ∀ x, ∑ i, c i * f i x = 0) :
    ∃ (m : ℕ) (d : Fin m → K) (v : Fin m → Fin n → k),
      (∀ j x, ∑ i, φ (v j i) * f i x = 0) ∧ ∀ i, c i = ∑ j, d j * φ (v j i) := by sorry
