-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_dvd_trd_mul_of_ne_of_ne
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_forall_dvd_trd_mul_of_ne_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/efb9024a-af58-590f-a539-21c43d1d5c7c
-- title:
--   Non-degeneracy of the trace pairing on Λ/ℓΛ
-- statement:
--   Let $a,b$ be rational numbers and let $q,q'$ be primes such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the base change $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or contains $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order in the sense of the project: $\Lambda$ contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$ and is finitely generated as a $\mathbb{Z}$-module, and every order containing $\Lambda$ equals $\Lambda$. Let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$. The assertion is that for every $w\in\Lambda$ such that for all $z\in\Lambda$ the reduced trace $\operatorname{trd}(wz)=2(wz)_{\mathrm{re}}$ is $\ell$ times an integer, there exists $w'\in\Lambda$ with $w=\ell\cdot w'$ (the $\mathbb{Z}$-scalar action on $B$); that is, $w\in\ell\Lambda$.
--
--   This is the non-degeneracy of the reduced trace pairing $(x,y)\mapsto\operatorname{trd}(xy)$ on $\Lambda/\ell\Lambda$ for a maximal order $\Lambda$ at a prime $\ell$ where $B$ is unramified; equivalently, the dual lattice of $\Lambda$ with respect to $\operatorname{trd}$ has no $\ell$-torsion contribution beyond $\Lambda$ itself. It is used to identify the elements of $\Lambda$ whose products have reduced trace divisible by $\ell$ with membership in a suitable sublattice, in the statement [`QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_forall_dvd_trd_mul_of_ne_of_ne.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_forall_dvd_trd_mul_of_ne_of_ne
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∀ w ∈ Λ, (∀ z ∈ Λ, ∃ t : ℤ, trd (w * z) = (ℓ : ℚ) * t) → ∃ w' ∈ Λ, w = (ℓ : ℤ) • w' := by sorry
