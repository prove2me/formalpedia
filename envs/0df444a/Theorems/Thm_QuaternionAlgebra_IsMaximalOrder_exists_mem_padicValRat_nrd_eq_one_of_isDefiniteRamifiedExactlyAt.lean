-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/45cab60d-0029-50b5-910a-dcc071c06271
-- title:
--   A uniformiser of reduced norm valuation one in a maximal order
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a natural number carrying the typeclass assumption that it is prime. Assume the project's definiteness-and-ramification hypothesis `IsDefiniteRamifiedExactlyAt a b q'`, namely: $a<0$, $b<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the property that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit holds if and only if the image of $q'$ lies in the prime ideal $v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order in the project's sense: $\Lambda$ is an order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated over $\mathbb{Z}$; and every order $\Lambda'$ containing $\Lambda$ equals $\Lambda$. The conclusion is that there exists $h\in\Lambda$ with $h\neq 0$ whose reduced norm $\mathrm{nrd}\,h=h_{\mathrm{re}}^2-a\,h_{\mathrm{imI}}^2-b\,h_{\mathrm{imJ}}^2+ab\,h_{\mathrm{imK}}^2$ satisfies $\mathrm{padicValRat}\;q'\,(\mathrm{nrd}\,h)=1$, i.e. its $q'$-adic valuation is exactly one.
--
--   This expresses, inside a maximal order of the definite rational quaternion algebra ramified exactly at $q'$, that the local division algebra at $q'$ has ramification index two: $\Lambda$ contains an element whose reduced norm is exactly divisible by $q'$, a uniformiser of the local order. It is used in the project's analysis of orders under multiplication by finite ideles and in the construction of matrix representations for the indefinite ramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ h ∈ Λ, h ≠ 0 ∧ padicValRat q' (QuaternionAlgebra.nrd h) = 1 := by sorry
