-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/072a767c-4ed8-53e3-b542-ebebab06eefd
-- title:
--   A left generator of the ramified prime normalises a maximal order
-- statement:
--   Fix rationals $a,b$ and natural numbers $q,q'$, each assumed prime. Suppose $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or contains $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $r$ be $q$ or $q'$, and let $\pi\in\Lambda$ be such that for every $m\in\Lambda$ the reduced norm $\mathrm{nrd}\,m=m_{\mathrm{re}}^2-a\,m_{i}^2-b\,m_{j}^2+ab\,m_{k}^2$ is an integral multiple of $r$ if and only if $m=l\pi$ for some $l\in\Lambda$; thus $\pi$ generates, as a left ideal, the set of elements of $\Lambda$ whose reduced norm is divisible by $r$. The conclusion is twofold: for every $x\in\Lambda$ there is $y\in\Lambda$ with $\pi x=y\pi$, and for every $x\in\Lambda$ there is $y\in\Lambda$ with $x\pi=\pi y$; that is, $\pi\Lambda\subseteq\Lambda\pi$ and $\Lambda\pi\subseteq\pi\Lambda$.
--
--   This is the statement that a left generator of the two-sided prime of $\Lambda$ above a ramified place normalises $\Lambda$, so that conjugation by $\pi$ preserves the maximal order. It is used in the construction of a generator of the ramified prime, [`QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_generator_ramifiedPrime_of_isIndefiniteRamifiedExactlyAt), and rests on the integrality of reduced norms on orders together with the classification of the $\Lambda$-stable lattices between $r\Lambda$ and $\Lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt.lean

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

theorem QuaternionAlgebra.IsMaximalOrder.forall_exists_mul_eq_mul_of_forall_dvd_nrd_iff_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (π : ℍ[ℚ, a, b]) (hπ : π ∈ Λ)
    (hgen : ∀ m ∈ Λ, (∃ n : ℤ, nrd m = (r : ℚ) * n) ↔ ∃ l ∈ Λ, m = l * π) :
    (∀ x ∈ Λ, ∃ y ∈ Λ, π * x = y * π) ∧ (∀ x ∈ Λ, ∃ y ∈ Λ, x * π = π * y) := by sorry
