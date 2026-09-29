-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/bbd3e465-d9a5-559b-8c96-aee9d909a502
-- title:
--   Element of a maximal order irreducible modulo a ramified prime
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes. Assume $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has the property that every nonzero element is a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $\mathbb{H}[\mathbb{Q},a,b]$, it is finitely generated over $\mathbb{Z}$, and every order containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r=q$ or $r=q'$. Then there exist $\theta\in\Lambda$ and integers $t,n$ such that the reduced trace $\mathrm{trd}\,\theta=2\theta_{\mathrm{re}}$ equals $t$, the reduced norm $\mathrm{nrd}\,\theta=\theta_{\mathrm{re}}^2-a\theta_{i}^2-b\theta_{j}^2+ab\theta_{k}^2$ equals $n$, and the polynomial $x^2-tx+n$ has no root in $\mathbb{Z}/r\mathbb{Z}$: for all $x\in\mathbb{Z}/r\mathbb{Z}$, $x^2-\bar{t}x+\bar{n}\neq 0$.
--
--   This records that a maximal order in an indefinite quaternion algebra ramified exactly at $q$ and $q'$ contains an element whose reduced characteristic polynomial stays irreducible modulo either ramified prime, reflecting that the residue algebra of the order at a ramified prime is the quadratic extension of $\mathbb{F}_r$. It is used in the construction of coordinates for maximal orders in the Čerednik–Drinfel'd setting and in the accompanying divisibility and trace-form statements at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (r : ℕ) (hr : r = q ∨ r = q') :
    ∃ θ ∈ Λ, ∃ t n : ℤ, trd θ = (t : ℚ) ∧ nrd θ = (n : ℚ) ∧
      ∀ x : ZMod r, x ^ 2 - (t : ZMod r) * x + (n : ZMod r) ≠ 0 := by sorry
