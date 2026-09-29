-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/8687ee75-a51d-53f8-83ff-95d81daba6da
-- title:
--   Reduced norm divisible by r² forces h ∈ rΛ
-- statement:
--   Fix rationals $a,b$ and natural numbers $q,q'$, each assumed prime. Suppose the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or contains $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order, meaning: $1 \in \Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $B$, $\Lambda$ is finitely generated over $\mathbb{Z}$, and every order $\Lambda'$ containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r = q$ or $r = q'$. Then for every $h \in \Lambda$ such that either $h = 0$ or the $r$-adic valuation of the reduced norm $\operatorname{nrd} h = h_{\mathrm{re}}^2 - a\,h_{\mathrm{imI}}^2 - b\,h_{\mathrm{imJ}}^2 + ab\,h_{\mathrm{imK}}^2$ is at least $2$, there exists $h' \in \Lambda$ with $h = r \cdot h'$ (scalar action of $(r : \mathbb{Z})$).
--
--   This is the local statement that at a ramified place $r$ of an indefinite rational quaternion algebra the completed maximal order is the valuation ring of the division algebra $B \otimes \mathbb{Q}_r$, so that its unique maximal two-sided ideal has square $r\Lambda$: elements of reduced norm of valuation $\ge 2$ lie in $r\Lambda$. It is used in the analysis of the two-sided ideal structure of $\Lambda$ at $q$ and $q'$, in particular for the existence of an element whose reduced norm is exactly divisible by $r$ and for the identification of the left ideals above a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt.lean

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

theorem QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat r (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (r : ℤ) • h' := by sorry
