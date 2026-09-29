-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/94ac2d2e-9827-5307-b780-655fdfea9dc7
-- title:
--   Norm-one unit congruent mod N to a given element of a maximal order
-- statement:
--   Let $N$ be a nonzero natural number and let $q,q'$ be primes with $q \nmid N$, $q' \nmid N$ and $q' \neq q$. Let $a,b \in \mathbb{Q}$ and consider the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, assumed to satisfy `IsIndefiniteRamifiedExactlyAt`, that is: $a > 0$ or $b > 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element a unit) exactly when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order, i.e. $1 \in \Lambda$, $\Lambda$ is closed under multiplication, finitely generated, spans the algebra over $\mathbb{Q}$, and every order containing $\Lambda$ equals $\Lambda$. Let $c \in \Lambda$ and $k \in \mathbb{Z}$ with reduced norm $\mathrm{nrd}(c) = c_{\mathrm{re}}^2 - a\,c_I^2 - b\,c_J^2 + ab\,c_K^2$ equal to $1 + Nk$. Then there exists $u \in \mathbb{H}[\mathbb{Q},a,b]$ lying in $\Lambda$ and invertible in $\Lambda$ (some $v \in \Lambda$ with $uv = vu = 1$), with $\mathrm{nrd}(u) = 1$, and some $z \in \Lambda$ such that $u - c = N \cdot z$.
--
--   This is the strong approximation statement for the norm-one group of an indefinite rational quaternion algebra, in the concrete form: an element of a maximal order whose reduced norm is congruent to $1$ modulo $N$ can be adjusted modulo $N\Lambda$ to a unit of reduced norm $1$. It is used in the study of Eichler orders and their level structures, in particular in the comparison of level-$N$ module data with units of reduced norm one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq.lean

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

theorem QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ ∃ z ∈ Λ, u - c = (N : ℤ) • z := by sorry
