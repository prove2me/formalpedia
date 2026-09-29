-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/0928ffe8-082a-5d86-98c4-f32b7b46aa08
-- title:
--   Trace divisibility modulo a ramified prime forces rmidnrd
-- statement:
--   Let $a,b$ be rationals and let $q,q'$ be primes, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order in the sense of `IsMaximalOrder`: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$ and is finitely generated as a $\mathbb{Z}$-module, and every order containing it is equal to it. Let $r$ be a natural number with $r=q$ or $r=q'$. The conclusion is that for every $w\in\Lambda$, if for every $z\in\Lambda$ there is an integer $t$ with $\operatorname{trd}(wz)=rt$, where $\operatorname{trd}(x)=2x_{\mathrm{re}}$, then there is an integer $n$ with $\operatorname{nrd}(w)=rn$, where $\operatorname{nrd}(x)=x_{\mathrm{re}}^2-ax_{\mathrm{imI}}^2-bx_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$.
--
--   This identifies the radical of the reduced trace pairing on $\Lambda/r\Lambda$ as being contained in the unique two-sided maximal ideal $\mathfrak{P}=\{x\in\Lambda : r\mid\operatorname{nrd}(x)\}$ above a ramified prime $r$ of the indefinite quaternion algebra. It is used in the local study of $\Lambda$ at $q$ and $q'$, feeding the criteria for membership in $\mathfrak{P}$ and for divisibility by $r$ of elements of $\Lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∀ w ∈ Λ, (∀ z ∈ Λ, ∃ t : ℤ, trd (w * z) = (r : ℚ) * t) → ∃ n : ℤ, nrd w = (r : ℚ) * n := by sorry
