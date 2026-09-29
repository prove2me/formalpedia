-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_isMaximalOrder
-- name    : QuaternionAlgebra.exists_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/a799b400-4957-5ea3-8db2-0c3e57668902
-- title:
--   Existence of a maximal ℤ-order in (a,bℚ)
-- statement:
--   Let $a$ and $b$ be rational numbers, both assumed non-zero, and let $\mathbb{H}[\mathbb{Q},a,b]$ denote the associated quaternion algebra over $\mathbb{Q}$, i.e. the $\mathbb{Q}$-algebra with basis $1,i,j,ij$ and relations $i^2=a$, $j^2=b$, $ij=-ji$. The assertion is that there exists a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ satisfying [`QuaternionAlgebra.IsMaximalOrder`](def/QuaternionAlgebra_EichlerOrder.html#L63), which by definition means two things. First, $\Lambda$ is an order in the sense of the predicate `IsOrder`: it contains $1$; it is closed under multiplication, so that $xy \in \Lambda$ whenever $x,y \in \Lambda$; its $\mathbb{Q}$-span inside $\mathbb{H}[\mathbb{Q},a,b]$ is the whole algebra; and it is finitely generated as a $\mathbb{Z}$-module. Secondly, $\Lambda$ is maximal among such orders in the strong sense that every $\mathbb{Z}$-submodule $\Lambda'$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is again an order in the above sense and satisfies $\Lambda \le \Lambda'$ is in fact equal to $\Lambda$. The statement is a pure existence statement: no maximal order is named, and no uniqueness or local description is claimed.
--
--   This is the classical existence of maximal orders in a quaternion algebra over $\mathbb{Q}$, the case over $\mathbb{Z}$ of the existence of maximal orders in a separable algebra over a Dedekind domain. It is used downstream in the construction of Eichler orders of given level in definite and indefinite quaternion algebras ramified at prescribed sets of places, and in the construction of the fake elliptic curves used in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_isMaximalOrder.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_isMaximalOrder (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsMaximalOrder Λ := by sorry
