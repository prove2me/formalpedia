-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
-- name    : QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/767ae7bc-7b98-518e-963b-62cd78069adb
-- title:
--   Maximal orders force a ≠ 0 and b ≠ 0
-- statement:
--   Let $a, b$ be rational numbers and let $\mathbb{H}[\mathbb{Q},a,b]$ be the rational quaternion algebra with basis $1, i, j, k$ and relations $i^2 = a$, $j^2 = b$, $k = ij = -ji$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order in the sense of the project's predicate `IsMaximalOrder`: first, $\Lambda$ is an order, that is, $1 \in \Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module; and second, $\Lambda$ is maximal among such orders, in the sense that every $\mathbb{Z}$-submodule $\Lambda'$ satisfying these four conditions and containing $\Lambda$ is equal to $\Lambda$. The conclusion is the conjunction $a \neq 0$ and $b \neq 0$; equivalently, a rational quaternion algebra with a degenerate structure constant admits no maximal order at all.
--
--   This is the standard fact that an algebra with a nonzero nilpotent two-sided ideal has no maximal order, specialised to the degenerate rational quaternion algebras $(0,b)$ and $(a,0)$. It serves as a bridge lemma allowing downstream statements in the Čerednik–Drinfel'd and Eichler-order material to hypothesise only that a lattice is a maximal order, while still working with an honest quaternion algebra in which $i^2$ and $j^2$ are invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) : a ≠ 0 ∧ b ≠ 0 := by sorry
