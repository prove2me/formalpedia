-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_le_mul_mem_relIndex_eq_sq
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_submodule_le_mul_mem_relIndex_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/5ee7fb63-6bac-504d-997d-11b7fac633d5
-- title:
--   Left ideal of index ℓ² in a maximal quaternion order
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes with $q'\neq q$, and suppose that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or contains $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, $\Lambda$ spans $B$ over $\mathbb{Q}$ and is finitely generated over $\mathbb{Z}$, and every order containing $\Lambda$ equals $\Lambda$. Let $\ell$ be any prime, with no condition relating $\ell$ to $q$ or $q'$. Then there exists a $\mathbb{Z}$-submodule $L_0$ of $B$ such that $L_0\subseteq\Lambda$; $\ell x\in L_0$ for every $x\in\Lambda$ (so $\ell\Lambda\subseteq L_0$); $yx\in L_0$ for every $y\in\Lambda$ and every $x\in L_0$, so that $L_0$ is stable under left multiplication by $\Lambda$; and the relative index of the additive subgroup $L_0$ in the additive subgroup $\Lambda$ equals $\ell^2$.
--
--   This is the existence, at an arbitrary prime $\ell$, of a left ideal of a maximal order in an indefinite quaternion algebra over $\mathbb{Q}$ ramified exactly at two primes, of index $\ell^2$ and containing $\ell\Lambda$ — in the split case the preimage of the annihilator of a line in $\Lambda/\ell\Lambda\cong M_2(\mathbb{F}_\ell)$, in the ramified case the preimage of the maximal ideal of the local division algebra. It supplies the level structure used in the statements about coarse moduli of the quaternionic Shimura curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_le_mul_mem_relIndex_eq_sq.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_submodule_le_mul_mem_relIndex_eq_sq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ L₀ : Submodule ℤ ℍ[ℚ, a, b], L₀ ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) ∧
      L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by sorry
