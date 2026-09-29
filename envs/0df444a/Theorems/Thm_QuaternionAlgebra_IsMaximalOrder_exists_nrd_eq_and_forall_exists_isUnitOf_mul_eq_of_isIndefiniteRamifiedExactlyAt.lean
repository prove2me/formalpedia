-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4630a1cd-c50e-5088-a9e3-f52e59f1f690
-- title:
--   Norm-r elements in a maximal order at a ramified prime
-- statement:
--   Let $q$ and $q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is the whole algebra, it is finitely generated over $\mathbb{Z}$, and every order containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r=q$ or $r=q'$. Then, writing $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$: (i) there exists $s\in\Lambda$ with $\mathrm{nrd}(s)=r$; and (ii) for all $s,s'\in\Lambda$ with $\mathrm{nrd}(s)=\mathrm{nrd}(s')=r$ there is $u\in\mathbb{H}[\mathbb{Q},a,b]$ with $u\in\Lambda$ admitting a two-sided inverse inside $\Lambda$, with $\mathrm{nrd}(u)=1$, and with $us=s'$.
--
--   This is the statement that at a ramified prime $r$ of an indefinite rational quaternion algebra the norm-$r$ elements of a maximal order form a single orbit under left multiplication by norm-one units — equivalently, that the two-sided prime above $r$ is principal with any norm-$r$ element as generator. It underlies the Atkin–Lehner involution at $r$ in the Čerednik–Drinfeld description of Shimura curves, and is used in the corresponding Hecke/Atkin–Lehner comparison for fake elliptic curves and in the Eichler-order analogue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    (∃ s ∈ Λ, nrd s = (r : ℚ)) ∧
    (∀ s s' : ℍ[ℚ, a, b], s ∈ Λ → s' ∈ Λ → nrd s = (r : ℚ) → nrd s' = (r : ℚ) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * s = s') := by sorry
