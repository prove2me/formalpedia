-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
-- name    : QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/10fcb489-734e-5f01-85d7-e4facf20144f
-- title:
--   Transport of a left Λ-line modulo ℓ along w
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order in the sense of the project's `IsOrder`: it contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, and is finitely generated. Let $\ell$ be a natural number and $J$ a $\mathbb{Z}$-submodule with $J\le\Lambda$, such that $\ell x\in J$ for every $x\in\Lambda$, such that $yx\in J$ whenever $y\in\Lambda$ and $x\in J$, and such that the relative index of the additive subgroup of $J$ in that of $\Lambda$ equals $\ell^2$. Let $w\in\Lambda$ admit a left inverse modulo $\ell\Lambda$, i.e. there are $w',y\in\Lambda$ with $w'w-1=\ell y$. Then there exists a $\mathbb{Z}$-submodule $L_0\le\Lambda$ with the same four properties — $\ell\Lambda\subseteq L_0$, stability under left multiplication by elements of $\Lambda$, and relative index $\ell^2$ in $\Lambda$ — which moreover satisfies $L_0=\{z\in\Lambda: zw\in J\}$ elementwise, and for which $x\in J$ holds exactly when $x=zw+\ell y$ for some $z\in L_0$ and some $y\in\Lambda$.
--
--   This is the lattice-theoretic transport step saying that right multiplication by an element of $\Lambda$ invertible modulo $\ell$ permutes the left $\Lambda$-stable submodules of index $\ell^2$ between $\ell\Lambda$ and $\Lambda$ (the "lines modulo $\ell$"), with $L_0w+\ell\Lambda=J$. It is used in the Čerednik–Drinfel'd part of the development, in the construction of algebraic families with extra level structure on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.exists_submodule_forall_mem_iff_mul_mem_relIndex_eq_sq_of_mul_sub_one_eq_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : J ≤ Λ) (hℓJ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ J)
    (hJ_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ J → (y : ℍ[ℚ, a, b]) * x ∈ J)
    (hJ_index : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (w : ↥Λ) (hwu : ∃ w' : ↥Λ, ∃ y : ↥Λ, (w' : ℍ[ℚ, a, b]) * (w : ℍ[ℚ, a, b]) - 1 = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ L₀ : Submodule ℤ ℍ[ℚ, a, b], L₀ ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) ∧
      L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧

      (∀ z : ℍ[ℚ, a, b], z ∈ L₀ ↔ z ∈ Λ ∧ z * (w : ℍ[ℚ, a, b]) ∈ J) ∧

      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔
        ∃ z ∈ L₀, ∃ y : ↥Λ, x = z * (w : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
