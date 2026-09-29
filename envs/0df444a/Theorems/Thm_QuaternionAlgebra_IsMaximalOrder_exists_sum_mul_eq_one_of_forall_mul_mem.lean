-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_sum_mul_eq_one_of_forall_mul_mem
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_sum_mul_eq_one_of_forall_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/ba412c55-668a-5b9b-8db8-0fd1df671a8f
-- title:
--   Full-rank right ideals of a maximal order are invertible
-- statement:
--   Let $c,d$ be rationals and $q$ a prime, and suppose the quaternion algebra $H=\mathbb{H}[\mathbb{Q},c,d]$ satisfies `IsDefiniteRamifiedExactlyAt c d q`, i.e. $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the base change $H\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every non-zero element is a unit) precisely when $q$ lies in the prime ideal attached to $v$. Let $O$ be a $\mathbb{Z}$-submodule of $H$ which is a maximal order: it contains $1$, is closed under multiplication, its $\mathbb{Q}$-span is all of $H$, it is finitely generated over $\mathbb{Z}$, and every order containing it equals it. Let $I$ be a $\mathbb{Z}$-submodule of $H$ with $I\subseteq O$, stable under right multiplication by $O$ ($z\in I$, $o\in O$ imply $zo\in I$), and of full rank in the sense that $nO\subseteq I$ for some non-zero integer $n$. Then there exist a finite subset $t\subseteq H$ and a function $y:H\to H$ such that every $x\in t$ lies in $I$, for every $x\in t$ one has $y(x)\,z\in O$ for all $z\in I$, and $\sum_{x\in t} x\,y(x)=1$. (The elements of $I$ occurring in the sum serve as their own index set.)
--
--   This is the invertibility of a full-rank integral right ideal of a maximal order in a definite rational quaternion algebra: writing $I^{-1}=\{y\in H: yI\subseteq O\}$, the conclusion says $1\in I\cdot I^{-1}$, so $I$ is an invertible, hence projective, right $O$-module. It feeds the construction of matrices implementing membership in such ideals, used in [`QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_sum_mul_eq_one_of_forall_mul_mem.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_sum_mul_eq_one_of_forall_mul_mem
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (I : Submodule ℤ ℍ[ℚ, c, d]) (hIO : I ≤ O) (hmul : ∀ z ∈ I, ∀ o ∈ O, z * o ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I) :
    ∃ (t : Finset ℍ[ℚ, c, d]) (y : ℍ[ℚ, c, d] → ℍ[ℚ, c, d]),
      (∀ x ∈ t, x ∈ I) ∧ (∀ x ∈ t, ∀ z ∈ I, y x * z ∈ O) ∧ ∑ x ∈ t, x * y x = 1 := by sorry
