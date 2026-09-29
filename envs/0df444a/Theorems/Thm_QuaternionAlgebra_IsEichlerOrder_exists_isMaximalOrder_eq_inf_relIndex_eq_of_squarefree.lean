-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f7c61cb7-0bfc-5f02-bce9-2c1677e7c171
-- title:
--   Prescribing one maximal over-order of a squarefree-level Eichler order
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is definite and ramified exactly at $q'$ in the sense of `IsDefiniteRamifiedExactlyAt`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q'$ lies in the prime ideal of $v$. Let $M$ be a nonzero squarefree natural number, and let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$. Assume $\Lambda$ is a maximal order, i.e. $\Lambda$ is an order ($1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is the whole algebra, and it is finitely generated over $\mathbb{Z}$) and every order containing $\Lambda$ equals $\Lambda$; and assume $R$ is an Eichler order of level $M$, i.e. there are maximal orders $\Lambda_1,\Lambda_2$ with $R=\Lambda_1\cap\Lambda_2$ and the relative index of the additive subgroup $R$ in $\Lambda_1$ equal to $M$. Assume finally $R\le\Lambda$. Then there exists a maximal order $\Lambda_2$ of $\mathbb{H}[\mathbb{Q},a,b]$ with $R=\Lambda\cap\Lambda_2$ and with the relative index of $R$ in $\Lambda$, as additive subgroups, equal to $M$.
--
--   This is the statement that for squarefree level any maximal order containing an Eichler order may be taken as one of the two maximal orders cutting it out, the index being $M$ in every such over-order; locally at the primes dividing $M$ it expresses that the maximal over-orders of an Iwahori order are the two ends of an edge of the Bruhat–Tits tree. It is used in the Čerednik–Drinfeld part of the development, where Eichler orders of squarefree level and their Hecke correspondences are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra

theorem QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {M : ℕ} [NeZero M] (hM : Squarefree M)
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R M) (hRΛ : R ≤ Λ) :
    ∃ Λ₂ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₂ ∧ R = Λ ⊓ Λ₂ ∧
      R.toAddSubgroup.relIndex Λ.toAddSubgroup = M := by sorry
