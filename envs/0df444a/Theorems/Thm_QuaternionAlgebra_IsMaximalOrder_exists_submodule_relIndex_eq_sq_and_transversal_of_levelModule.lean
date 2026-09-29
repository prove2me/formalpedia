-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/dc966885-d1ea-51ea-b8c9-62c994889afd
-- title:
--   A left Λ-ideal of index ℓ² transversal to a level module
-- statement:
--   Let $N$ be a nonzero squarefree natural number, let $q$ and $q'$ be primes with $q' \neq q$ and $q \nmid N$, $q' \nmid N$, and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order, i.e. $1 \in \Lambda$, $\Lambda$ is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $J'$ be a $\mathbb{Z}$-submodule of $B$ with $\Lambda \subseteq J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$ and $[J' : \Lambda] = N^2$ (as the relative index of the underlying additive subgroups). Let $\ell$ be a prime with $\ell \neq q$ and $\ell \neq q'$ (the case $\ell \mid N$ is allowed). Then there exists a $\mathbb{Z}$-submodule $J \subseteq \Lambda$ of $B$ with $\ell\Lambda \subseteq J$, $\Lambda J \subseteq J$, relative index $[\Lambda : J] = \ell^2$, and such that every $y \in J'$ with $\ell y \in J$ lies in $\Lambda$.
--
--   The submodule $J$ is a left $\Lambda$-ideal corresponding to a line in $\Lambda/\ell\Lambda \cong M_2(\mathbb{F}_\ell)$ chosen transversal to the line determined by the level-$N$ module $J'$; this is the extra level structure at $\ell$ underlying the Hecke correspondence at a prime dividing the level. It is used in the construction of Eichler orders and their level structures for the quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra
open CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧ (∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ) := by sorry
