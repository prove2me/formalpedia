-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/9a897492-6acf-58ad-aa35-e4609434200d
-- title:
--   Maximal orders contain an element of reduced norm valuation one
-- statement:
--   Let $a,b\in\mathbb{Q}$ and consider the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $p$ be a prime number, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ with $p\in v$ (so $v$ is the place above $p$). Assume that every non-zero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$, the base change to the $v$-adic completion of $\mathbb{Q}$, is a unit, i.e. the completed algebra is a division algebra. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ satisfying `IsMaximalOrder`: it is an order, in the sense that $1\in\Lambda$, that $\Lambda$ is closed under multiplication, that its $\mathbb{Q}$-span is all of $\mathbb{H}[\mathbb{Q},a,b]$ and that it is finitely generated as a $\mathbb{Z}$-module; and it is maximal, in the sense that every order $\Lambda'$ with $\Lambda\le\Lambda'$ equals $\Lambda$. Then there exists $h\in\Lambda$ with $h\neq 0$ whose reduced norm $\mathrm{nrd}(h)=h_{\mathrm{re}}^2-a\,h_{\mathrm{I}}^2-b\,h_{\mathrm{J}}^2+ab\,h_{\mathrm{K}}^2$ has $p$-adic valuation exactly $1$.
--
--   At a place where a rational quaternion algebra ramifies, the unique two-sided prime of a maximal order above $p$ has square $p\Lambda$; the existence of an element of reduced norm of valuation one is the corresponding statement that this prime strictly contains $p\Lambda$, equivalently that the local ramification index is $2$. It is used in the analysis of $\Lambda/p\Lambda$ and of the residue structure of maximal orders at ramified primes, through [`QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ h ∈ Λ, h ≠ 0 ∧ padicValRat p (QuaternionAlgebra.nrd h) = 1 := by sorry
