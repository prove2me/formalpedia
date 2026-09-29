-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
-- name    : QuaternionAlgebra.IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/251e41fd-88e4-5dbf-8852-65cf899e1fc9
-- title:
--   Index of Λ-stable subgroups between ℓΛ and Λ
-- statement:
--   Let $a,b\in\mathbb Q$ and let $q,q'$ be primes such that the quaternion algebra $B=\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $B\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element is a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, $\Lambda$ spans $B$ over $\mathbb Q$, $\Lambda$ is finitely generated, and every $\mathbb Z$-submodule with these four properties containing $\Lambda$ equals $\Lambda$. Let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$, and let $J\subseteq B$ be a $\mathbb Z$-submodule with $J\subseteq\Lambda$, with $\ell y\in J$ for all $y\in\Lambda$, and with $mx\in J$ for all $m\in\Lambda$, $x\in J$. Then the relative index of the additive subgroup underlying the $\mathbb Z$-span of $\ell\Lambda=\{\ell y: y\in\Lambda\}$ in the additive subgroup underlying $J$ — that is, the index of $(\mathbb Z\text{-span of }\ell\Lambda)\cap J$ in $J$ — is $1$, $\ell^2$ or $\ell^4$.
--
--   Since $\ell$ is unramified in $B$, the quotient $\Lambda/\ell\Lambda$ is isomorphic to $M_2(\mathbb F_\ell)$, and the statement is the classification of left ideals of $M_2(\mathbb F_\ell)$ by the dimension $0,1,2$ of the corresponding subspace of $\mathbb F_\ell^2$, transported to $\Lambda$-stable subgroups between $\ell\Lambda$ and $\Lambda$. It feeds the comparison of Hecke neighbours with level-$\ell$ isogenies for fake elliptic curves, and the construction of chains of subgroups of square relative index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex J.toAddSubgroup ∈
      ({1, ℓ ^ 2, ℓ ^ 4} : Set ℕ) := by sorry
