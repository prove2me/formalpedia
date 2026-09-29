-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/534d861e-9241-58bf-8734-e2a4188b3f46
-- title:
--   At a ramified prime, r ∣ nrd implies r ∣ trd
-- statement:
--   Let $a,b\in\mathbb Q$ and let $q,q'$ be primes, and suppose the quaternion algebra $B=\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$ the completed algebra $B\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule which is a maximal order, that is: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb Q$-span is all of $B$ and it is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r=q$ or $r=q'$. Then for every $x\in\Lambda$ whose reduced norm $\mathrm{nrd}\,x=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$ is of the form $r\cdot n$ with $n\in\mathbb Z$, the reduced trace $\mathrm{trd}\,x=2x_{\mathrm{re}}$ is of the form $r\cdot t$ with $t\in\mathbb Z$, both equalities being equalities in $\mathbb Q$.
--
--   This is the divisibility statement that the unique two-sided maximal ideal of a maximal order above a ramified prime $r$ consists of elements of reduced trace divisible by $r$; it fails at split primes, where $\mathrm{diag}(r,1)$ has norm $r$ and trace $r+1$. It is used in the congruence computations for the quaternionic level structures, being cited by [`QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt) and [`QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∀ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → ∃ t : ℤ, trd x = (r : ℚ) * t := by sorry
