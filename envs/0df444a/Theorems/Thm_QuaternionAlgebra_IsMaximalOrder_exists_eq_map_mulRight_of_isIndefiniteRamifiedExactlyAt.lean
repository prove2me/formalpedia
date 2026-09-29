-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d2e85eac-21a2-5c83-9c4e-a53a92f0d558
-- title:
--   Left ideals of an indefinite maximal order are principal
-- statement:
--   Let $q,q'$ be primes, let $a,b\in\mathbb{Q}$, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the rational quaternion algebra with $i^2=a$, $j^2=b$. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has every nonzero element a unit precisely when $v$ contains the image of $q$ or of $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order in the sense that it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated as a $\mathbb{Z}$-module, and that every order containing $\Lambda$ equals $\Lambda$. Let $I$ be a $\mathbb{Z}$-submodule of $B$ which is finitely generated, whose $\mathbb{Q}$-span is all of $B$, and which satisfies $x y \in I$ for all $x\in\Lambda$, $y\in I$. The conclusion is that there is an element $x_0\in B$ with $x_0\neq 0$ such that for every $y\in B$ one has $y\in I$ if and only if $y=z x_0$ for some $z\in\Lambda$; that is, $I=\Lambda x_0$.
--
--   This is the statement that a maximal order in an indefinite rational quaternion algebra ramified exactly at two primes has class number one in the strong form that every full left $\Lambda$-lattice is principal, a result going back to Eichler and proved through strong approximation for the norm-one group. It is used in the construction of the Čerednik–Drinfeld setting and in the study of Eichler orders, for instance by [`CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder) and [`QuaternionAlgebra.IsEichlerOrder.exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_units_mem_nrd_eq_level_forall_mem_iff_conj_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIfg : I.FG) (hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤)
    (hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I) :
    ∃ x₀ : ℍ[ℚ, a, b], x₀ ≠ 0 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ I ↔ ∃ z ∈ Λ, z * x₀ = y := by sorry
