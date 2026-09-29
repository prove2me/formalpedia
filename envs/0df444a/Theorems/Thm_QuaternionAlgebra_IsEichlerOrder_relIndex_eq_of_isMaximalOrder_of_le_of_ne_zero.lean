-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero
-- name    : QuaternionAlgebra.IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4a49a6ac-5196-5435-8901-19e9b738151d
-- title:
--   Index of an Eichler order in any containing maximal order
-- statement:
--   Let $a,b$ be nonzero rational numbers and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra. Here an order means a $\mathbb{Z}$-submodule $\Lambda$ of $B$ that contains $1$, is closed under multiplication, is finitely generated, and whose $\mathbb{Q}$-span is all of $B$; it is maximal when every order containing it equals it. Let $R$ be a $\mathbb{Z}$-submodule of $B$ and $N$ a natural number such that $R$ is an Eichler order of level $N$, that is, there are maximal orders $\Lambda_1,\Lambda_2$ with $R=\Lambda_1\cap\Lambda_2$ and such that the relative index of the additive group of $R$ in that of $\Lambda_1$ equals $N$. Let $\Lambda$ be any maximal order with $R\le\Lambda$. Then the relative index of the additive group of $R$ in that of $\Lambda$ is again $N$; since $R\le\Lambda$ this is the index $[\Lambda:R]$. No definiteness or ramification condition on $B$ is imposed beyond $a\neq0$ and $b\neq0$.
--
--   This is the statement that the level of an Eichler order is well defined: the index of $R$ in a maximal order containing it does not depend on which such maximal order is chosen. It is used in the construction of Eichler orders of squarefree level as intersections of maximal orders, and in the identification of the lattices attached to level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hle : R ≤ Λ) :
    R.toAddSubgroup.relIndex Λ.toAddSubgroup = N := by sorry
