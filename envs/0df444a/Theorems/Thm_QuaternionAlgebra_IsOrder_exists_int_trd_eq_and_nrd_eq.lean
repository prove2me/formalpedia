-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
-- name    : QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/7e2fe97c-ca12-5441-adc4-19121243e85d
-- title:
--   Reduced trace and norm of an element of a quaternion order are integral
-- statement:
--   Let $a,b$ be rational numbers and let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11): it contains $1$, it is closed under multiplication, its $\mathbb{Q}$-span is the whole algebra, and it is finitely generated as a $\mathbb{Z}$-module. Let $x$ be an element of $\Lambda$. Then two assertions hold. First, there are integers $t,n$ with $\operatorname{trd} x = t$ and $\operatorname{nrd} x = n$, where the reduced trace is $\operatorname{trd} x = 2x_{\mathrm{re}}$ and the reduced norm is $\operatorname{nrd} x = x_{\mathrm{re}}^{2} - a\,x_{\mathrm{imI}}^{2} - b\,x_{\mathrm{imJ}}^{2} + ab\,x_{\mathrm{imK}}^{2}$, the equalities being equalities of rationals with the images of $t$ and $n$. Second, for every rational $r$ such that $r \cdot 1$ lies in $\Lambda$ there is an integer $k$ with $k = r$; this second clause does not involve $x$ and says that the rational scalars belonging to $\Lambda$ are exactly the integral ones. No definiteness or nondegeneracy hypothesis is imposed on $a$ and $b$.
--
--   This is the standard fact that elements of an order in a quaternion algebra over $\mathbb{Q}$ are integral, so that their reduced traces and reduced norms lie in $\mathbb{Z}$, together with the determination of the scalars in an order. It is used in the orbit-counting and lattice arguments for orders and their unit groups in the Čerednik–Drinfel'd part of the development, for instance in locating elements of prescribed reduced norm and in the comparison of lattices attached to fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ t n : ℤ, QuaternionAlgebra.trd x = t ∧ QuaternionAlgebra.nrd x = n) ∧
      (∀ r : ℚ, r • (1 : ℍ[ℚ, a, b]) ∈ Λ → ∃ k : ℤ, (k : ℚ) = r) := by sorry
