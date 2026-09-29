-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/94944e25-91ce-5ac5-90ea-6d564a3ae375
-- title:
--   Trace-dual of a maximal order equals μ⁻¹Λ
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$ and write $B=\mathbb{H}[\mathbb{Q},a,b]$ for the associated quaternion algebra. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ to the $v$-adic completion has all its nonzero elements invertible precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $\Lambda$ contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$ and is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$ in $B$. Then for every $c\in B$ the following are equivalent: for all $x\in\Lambda$ the reduced trace $\operatorname{trd}(cx)=2(cx)_{\mathrm{re}}$ is an integer, i.e. equals $(n:\mathbb{Q})$ for some $n\in\mathbb{Z}$; and $\mu c\in\Lambda$.
--
--   This identifies the dual lattice (codifferent) of a maximal order $\Lambda$ in an indefinite rational quaternion algebra ramified exactly at $q$ and $q'$ with respect to the reduced-trace pairing as $\mu^{-1}\Lambda$, where $\mu\in\Lambda$ has $\mu^2=-qq'$; equivalently the different is $\mu\Lambda$, of reduced norm $qq'$. It is the arithmetic input to the perfectness of the $\star$-alternating form $\operatorname{trd}(\bar{x}\mu^{-1}y)$ and is cited by [`QuaternionAlgebra.IsMaximalOrder.isPerfPair_of_generator_of_alternating_starAdjoint_forms`](thm.html#QuaternionAlgebra.IsMaximalOrder.isPerfPair_of_generator_of_alternating_starAdjoint_forms) and by [`QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt) in the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (c : ℍ[ℚ, a, b]) :
    (∀ x ∈ Λ, ∃ n : ℤ, (n : ℚ) = trd (c * x)) ↔ (μ : ℍ[ℚ, a, b]) * c ∈ Λ := by sorry
