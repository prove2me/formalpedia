-- Prove2me | Theorems.Thm_TensorProduct_exists_pow_smul_eq_one_tmul
-- name    : TensorProduct.exists_pow_smul_eq_one_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/4990b119-829d-5800-8396-a92fe108e586
-- title:
--   Clearing denominators in ℚ_q ⊗_{ℤ_q} T
-- statement:
--   Let $q$ be a prime number, let $\mathbb{Z}_q$ denote the $q$-adic integers and $\mathbb{Q}_q$ the field of $q$-adic numbers, and let $T$ be an additive abelian group equipped with a $\mathbb{Z}_q$-module structure. The assertion is that for every element $w$ of the tensor product $\mathbb{Q}_q \otimes_{\mathbb{Z}_q} T$ there exist a natural number $k$ and an element $t \in T$ such that the scalar multiple of $w$ by $q^k \in \mathbb{Q}_q$ equals the elementary tensor $1 \otimes t$. Thus every element of $\mathbb{Q}_q \otimes_{\mathbb{Z}_q} T$ becomes, after multiplication by a sufficiently large power of $q$, the image of an element of $T$ under the map $t \mapsto 1 \otimes t$; equivalently, every element of the tensor product is of the form $q^{-k}(1 \otimes t)$. No hypothesis is imposed on $T$ beyond being a $\mathbb{Z}_q$-module: it need not be finitely generated, torsion-free or $q$-adically complete.
--
--   This is the standard denominator-clearing statement expressing $\mathbb{Q}_q \otimes_{\mathbb{Z}_q} T$ as the module of fractions $T[1/q]$, so that every vector of a rational Tate module is a $q$-power multiple of a vector coming from the integral module. It is used in [`ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit`](thm.html#ModularCurve.exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit) to rescale a vector obtained by linear algebra over $\mathbb{Q}_q$ to one lying in the image of the integral Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_exists_pow_smul_eq_one_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem TensorProduct.exists_pow_smul_eq_one_tmul (q : ℕ) [Fact q.Prime]
    (T : Type) [AddCommGroup T] [Module ℤ_[q] T] (w : ℚ_[q] ⊗[ℤ_[q]] T) :
    ∃ (k : ℕ) (t : T), ((q : ℚ_[q]) ^ k) • w = (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] t := by sorry
