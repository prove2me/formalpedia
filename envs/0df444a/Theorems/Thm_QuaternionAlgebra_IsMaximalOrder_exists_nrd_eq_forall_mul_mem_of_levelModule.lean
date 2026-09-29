-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mul_mem_of_levelModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/2bf96390-4c59-5c43-9c6e-499a67097ab1
-- title:
--   Matching level-N modules by an element of norm ≡ 1
-- statement:
--   Fix natural numbers $N, q, q'$ with $N \neq 0$, with $q$ and $q'$ prime, with $q \nmid N$ and $q' \nmid N$, and with $q' \neq q$, and rationals $a, b$. Assume the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $1 \in \Lambda$, $\Lambda$ is closed under multiplication, finitely generated, spans the algebra over $\mathbb{Q}$, and every order containing $\Lambda$ equals $\Lambda$. Assume $N$ squarefree, and let $J', J''$ be $\mathbb{Z}$-submodules each satisfying: it contains $\Lambda$, is stable under left multiplication by $\Lambda$, is carried into $\Lambda$ by multiplication by $N$, and has relative index $N^2$ over $\Lambda$ (as additive subgroups, so $[J:\Lambda] = N^2$). The conclusion: there exists $c \in \Lambda$ and an integer $k$ with $\mathrm{nrd}(c) = c_{\mathrm{re}}^2 - a\,c_I^2 - b\,c_J^2 + ab\,c_K^2 = 1 + Nk$, such that $y c \in J''$ for every $y \in J'$.
--
--   This is the finite, purely local-to-global combinatorial half of the statement that the norm-one units of a maximal order act transitively on its level-$N$ modules: an element of $\Lambda$ of reduced norm congruent to $1$ modulo $N$ carrying $J'$ into $J''$. It feeds into [`QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule), where such a $c$ is upgraded by strong approximation to a unit of reduced norm exactly $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule.lean

import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra
open CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mul_mem_of_levelModule
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (N : ℚ) * (k : ℚ)) ∧ ∀ y ∈ J', y * c ∈ J'' := by sorry
