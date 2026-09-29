-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem
-- name    : QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_forall_mul_star_mem_imp_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/48a03369-2d20-5d75-a398-ea4478c3d197
-- title:
--   Level identity for a norm-ℓ element versus transversality
-- statement:
--   Let $q,q'$ be primes, $N$ a nonzero natural number, and $a,b$ rationals such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height one prime $v$ of the ring of integers of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: containing $1$, closed under multiplication, $\mathbb{Q}$-spanning the algebra, finitely generated; and maximal among orders for inclusion), and let $R\le\Lambda$ be an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with the index of $R$ in $\Lambda_1$ equal to $N$. Let $J'$ be a $\mathbb{Z}$-submodule with $\Lambda\le J'$, $\Lambda J'\subseteq J'$, $N J'\subseteq\Lambda$, index of $\Lambda$ in $J'$ equal to $N^2$, and such that an element $x\in\Lambda$ lies in $R$ if and only if $J'x\subseteq J'$. Let $\ell$ be a prime and $t\in R$ with $\mathrm{nrd}(t)=\ell$, where $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{i}^2-b\,x_{j}^2+ab\,x_{k}^2$. Then the equality of subsets $\ell J'+\Lambda t=J't$ (stated elementwise: for every $x$, $x$ is of the form $\ell j+mt$ with $j\in J'$, $m\in\Lambda$, if and only if $x=jt$ for some $j\in J'$) holds if and only if every $j\in J'$ with $j\,\overline{t}\in\Lambda$ already lies in $\Lambda$.
--
--   This is the transversality criterion for the level identity attached to a quaternion element of reduced norm $\ell$ in an Eichler order, in the style of Shimura's treatment of Hecke correspondences on quaternionic curves: both sides express that the endomorphism $y\mapsto y\overline{t}$ of the finite group $J'/\Lambda$ is onto, respectively injective. It feeds the local trichotomy for the Hecke correspondence at $\ell$, being used by [`QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd`](thm.html#QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_forall_mul_star_mem_imp_mem.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_forall_mul_star_mem_imp_mem
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) := by sorry
