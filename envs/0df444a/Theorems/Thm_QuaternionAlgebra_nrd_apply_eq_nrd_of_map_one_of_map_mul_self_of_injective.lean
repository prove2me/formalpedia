-- Prove2me | Theorems.Thm_QuaternionAlgebra_nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective
-- name    : QuaternionAlgebra.nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/3afb16b3-22c3-58e6-9d7d-ea6937fdb199
-- title:
--   Unital injective square-preserving linear maps preserve the reduced norm
-- statement:
--   Let $K$ be a field and $a, b, a', b' \in K$, and consider the Mathlib quaternion algebras $\mathbb{H}[K,a,b]$ and $\mathbb{H}[K,a',b']$ (generators $i, j$ with $i^2 = a$, $j^2 = b$, $ij = -ji$). Let $\eta : \mathbb{H}[K,a,b] \to \mathbb{H}[K,a',b']$ be a $K$-linear map, assumed to satisfy $\eta(1) = 1$, to be injective, and to preserve squares in the sense that $\eta(x \cdot x) = \eta(x) \cdot \eta(x)$ for every $x \in \mathbb{H}[K,a,b]$; $\eta$ is not assumed multiplicative. Then for every $x \in \mathbb{H}[K,a,b]$ the reduced norms agree, $\mathrm{nrd}(\eta x) = \mathrm{nrd}(x)$, where [`QuaternionAlgebra.nrd`](def/QuaternionAlgebra_ReducedNorm.html#L11) is the coordinate expression $\mathrm{nrd}(z) = z_{\mathrm{re}}^2 - a\, z_{\mathrm{imI}}^2 - b\, z_{\mathrm{imJ}}^2 + a b\, z_{\mathrm{imK}}^2$ on $\mathbb{H}[K,a,b]$, and correspondingly with $a', b'$ on the target. No hypothesis is imposed on the characteristic of $K$ or on the nondegeneracy of the parameters $a, b, a', b'$.
--
--   This is the standard fact that a unital injective linear map of quaternion algebras respecting squares is an isometry for the reduced norm, the norm being recoverable from the quadratic relation satisfied by every quaternion. It is used in the comparison of local boxes attached to maximal orders, in [`QuaternionAlgebra.localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal`](thm.html#QuaternionAlgebra.localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective
    {K : Type} [Field K] {a b a' b' : K}
    (η : ℍ[K, a, b] →ₗ[K] ℍ[K, a', b']) (h1 : η 1 = 1) (hη : Function.Injective η)
    (hsq : ∀ x : ℍ[K, a, b], η (x * x) = η x * η x) (x : ℍ[K, a, b]) :
    QuaternionAlgebra.nrd (η x) = QuaternionAlgebra.nrd x := by sorry
