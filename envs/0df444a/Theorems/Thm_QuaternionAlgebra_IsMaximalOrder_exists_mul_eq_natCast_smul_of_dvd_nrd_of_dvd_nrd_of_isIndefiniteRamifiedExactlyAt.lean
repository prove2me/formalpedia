-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4f01c5e4-4f78-58de-be64-ed0844662adc
-- title:
--   mathfrak Pᵣ²⊆ rΛ for maximal orders, indefinite ramified case
-- statement:
--   Let $a,b\in\mathbb Q$ and let $B=\mathbb H[\mathbb Q,a,b]$ be the associated quaternion algebra, and let $q,q'$ be primes. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $B\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element is a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule which is a maximal order, in the sense that $\Lambda$ contains $1$, is closed under multiplication, spans $B$ over $\mathbb Q$ and is finitely generated, and that every order containing $\Lambda$ equals $\Lambda$. Let $r$ be a natural number with $r=q$ or $r=q'$. Then for all $x,x'\in\Lambda$ such that $\mathrm{nrd}\,x=r\,n$ and $\mathrm{nrd}\,x'=r\,n'$ for some integers $n,n'$, where $\mathrm{nrd}\,x=x_{\mathrm{re}}^2-a\,x_{i}^2-b\,x_{j}^2+ab\,x_{k}^2$, there exists $y\in\Lambda$ with $x\,x'=r\cdot y$. The primes $q$ and $q'$ are not assumed distinct.
--
--   This is the statement that the two-sided ideal $\mathfrak P_r=\{x\in\Lambda:r\mid\mathrm{nrd}\,x\}$ of a maximal order at a ramified prime $r$ satisfies $\mathfrak P_r^2\subseteq r\Lambda$, the local algebra at $r$ being a division algebra with uniformiser of reduced norm of valuation one. It is used in the Čerednik–Drinfeld part of the development, in the manipulation of lattices and Atkin–Lehner quotients attached to fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt.lean

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

theorem QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (r : ℕ) (hr : r = q ∨ r = q') :
    ∀ x ∈ Λ, ∀ x' ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → (∃ n : ℤ, nrd x' = (r : ℚ) * n) →
      ∃ y ∈ Λ, x * x' = (r : ℤ) • y := by sorry
