-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/71b6ff40-44a4-5179-b5a8-b28350771ab6
-- title:
--   Divisibility by p in a maximal order at a ramified prime
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra, with reduced norm $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$. Let $p$ be a prime number and let $v$ be a height one prime of the ring of integers of $\mathbb{Q}$ whose prime ideal contains the image of $p$. Assume that the $v$-adic completion of $B$, namely $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ for $\mathbb{Q}_v$ the adic completion of $\mathbb{Q}$ at $v$, is a division ring in the sense that each of its nonzero elements is a unit. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order, that is: $\Lambda$ contains $1$, is closed under multiplication, has $\mathbb{Q}$-span equal to $B$ and is finitely generated as a $\mathbb{Z}$-module, and every $\mathbb{Z}$-submodule $\Lambda'$ of $B$ with these four properties that contains $\Lambda$ is equal to $\Lambda$. Let $h\in\Lambda$ and suppose that either $h=0$ or $\mathrm{padicValRat}\,p\,(\mathrm{nrd}\,h)\ge 2$. Then there exists $h'\in\Lambda$ with $h=p\cdot h'$ (scalar multiplication by $p$ viewed as an integer).
--
--   This is the divisibility half of the description of the two-sided maximal ideal of a maximal order above a prime at which the quaternion algebra ramifies: together with the existence of an element of reduced norm of valuation exactly one it expresses that this ideal squares to $p\Lambda$. It is used in [`QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime), in the analysis of the reduction of a maximal order modulo a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat p (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (p : ℤ) • h' := by sorry
