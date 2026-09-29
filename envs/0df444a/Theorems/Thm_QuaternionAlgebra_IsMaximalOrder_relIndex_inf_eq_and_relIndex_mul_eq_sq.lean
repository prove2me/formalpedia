-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq
-- name    : QuaternionAlgebra.IsMaximalOrder.relIndex_inf_eq_and_relIndex_mul_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f47b47c4-087c-51c1-834a-4d734cfa7207
-- title:
--   Indices attached to two maximal orders in a rational quaternion algebra
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda,\Lambda'$ be $\mathbb{Z}$-submodules of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, each of which is a maximal order in the sense of the project: each contains $1$, is closed under multiplication, has $\mathbb{Q}$-span equal to the whole algebra and is finitely generated as a $\mathbb{Z}$-module, and each is maximal among submodules with these four properties (any such submodule containing it equals it). Let $N$ be a natural number with $N\neq 0$, and assume that the relative index of $(\Lambda\cap\Lambda')$ in $\Lambda$, taken between the underlying additive subgroups — that is, the index of $\Lambda\cap\Lambda'$ inside $\Lambda$ — equals $N$. The conclusion is twofold: first, the corresponding relative index of $\Lambda\cap\Lambda'$ in $\Lambda'$ is also $N$; second, the relative index of $\Lambda$ in the product submodule $\Lambda\Lambda'$ (the $\mathbb{Z}$-span of the products $xy$ with $x\in\Lambda$, $y\in\Lambda'$), i.e. the index of $\Lambda\cap\Lambda\Lambda'$ in $\Lambda\Lambda'$, equals $N^{2}$.
--
--   This is the standard symmetry of the connecting-ideal indices for a pair of maximal orders in a quaternion algebra over $\mathbb{Q}$: the intersection has the same index in either order, and the product lattice, which is the ideal connecting them, has the square of that index over each. It is used in the construction of level structures for Eichler orders, being cited by [`QuaternionAlgebra.IsEichlerOrder.exists_levelModule`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_levelModule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.relIndex_inf_eq_and_relIndex_mul_eq_sq
    {a b : ℚ} (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ')
    {N : ℕ} [NeZero N] (hN : (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup = N) :
    (Λ ⊓ Λ').toAddSubgroup.relIndex Λ'.toAddSubgroup = N ∧
      Λ.toAddSubgroup.relIndex (Λ * Λ').toAddSubgroup = N ^ 2 := by sorry
