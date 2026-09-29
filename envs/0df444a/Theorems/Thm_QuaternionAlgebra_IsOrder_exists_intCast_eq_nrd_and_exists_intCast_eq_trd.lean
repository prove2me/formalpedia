-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
-- name    : QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4d914c84-1cd8-5a6c-bdbe-9153f886f2b9
-- title:
--   Integrality of reduced norm and trace on an order
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$, with basis $1,i,j,k$ satisfying $i^2=a$, $j^2=b$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), that is: $1\in\Lambda$; $\Lambda$ is closed under multiplication ($x,y\in\Lambda$ implies $xy\in\Lambda$); the $\mathbb{Q}$-span of $\Lambda$ is the whole algebra; and $\Lambda$ is a finitely generated $\mathbb{Z}$-module. Let $x\in\Lambda$. The assertion is the conjunction of two statements: there is an integer $n$ whose image in $\mathbb{Q}$ equals $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{i}^2-b\,x_{j}^2+ab\,x_{k}^2$, and there is an integer $t$ whose image in $\mathbb{Q}$ equals $\mathrm{trd}(x)=2x_{\mathrm{re}}$. No hypothesis is imposed on $a$ and $b$; in particular the algebra need not be a division algebra.
--
--   This is the standard integrality statement for orders in a quaternion algebra: the reduced norm and reduced trace of an element of an order are rational integers. It is used throughout the arithmetic of quaternionic orders in this development, for instance in the computations of degrees and traces attached to quaternionic multiplication structures on polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd x) ∧ ∃ t : ℤ, (t : ℚ) = QuaternionAlgebra.trd x := by sorry
