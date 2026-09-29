-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/0a46b2bb-241f-573f-bf14-c6d4f3b328b3
-- title:
--   Norm-one units of a maximal order move level-N modules transitively
-- statement:
--   Fix natural numbers $N, q, q'$ with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and rationals $a, b$ such that the predicate `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$, that is: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ that is a maximal order, i.e. $1 \in \Lambda$, $\Lambda$ is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing $\Lambda$ equals $\Lambda$; and let $N$ be squarefree. Let $J', J''$ be $\mathbb{Z}$-submodules of $B$ each satisfying the four conditions $\Lambda \le J$, $xy \in J$ for all $x \in \Lambda$, $y \in J$, $Ny \in \Lambda$ for all $y \in J$, and relative index $N^2$ of the additive subgroup $\Lambda$ in the additive subgroup $J$. Then there exists $u \in B$ with $u \in \Lambda$ admitting a two-sided inverse in $\Lambda$, with reduced norm $\mathrm{nrd}\,u = u_{\mathrm{re}}^2 - a u_{\mathrm{I}}^2 - b u_{\mathrm{J}}^2 + ab\, u_{\mathrm{K}}^2$ equal to $1$, and such that for every $y \in B$ one has $y \in J''$ if and only if $y = y'u$ for some $y' \in J'$; that is, $J'' = J'u$.
--
--   This is the transitivity of the action of the norm-one unit group of a maximal order in an indefinite rational quaternion algebra on its level-$N$ modules, a strong-approximation statement underlying the comparison of level structures on Shimura curves. It feeds the constructions of Eichler orders of level $N$ and of their level structures, and is used in the analysis of period lattices and of conjugation-invariant level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule.lean

import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ J'' ↔ ∃ y' ∈ J', y = y' * u := by sorry
