-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
-- name    : QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/c171856a-8b41-5c1b-9abc-62e6a53807eb
-- title:
--   Left ideals between rΛ and a maximal order at a ramified prime
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes such that $B=\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$, in the sense that $0<a$ or $0<b$ and, for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements units precisely when $q$ or $q'$ lies in the prime ideal of $v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and any order containing it equals it. Let $r$ be a natural number with $r=q$ or $r=q'$, and write $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$. Then, first, the set $\mathfrak{P}_r=\{x\in\Lambda:\ r\mid \mathrm{nrd}(x)\text{ in }\mathbb{Z}\}$ satisfies: for $m\in\Lambda$ and $x\in\Lambda$ with $r\mid\mathrm{nrd}(x)$ one has $r\mid\mathrm{nrd}(mx)$; $r\mid\mathrm{nrd}(r\cdot y)$ for every $y\in\Lambda$; there is $x\in\Lambda$ with $r\mid\mathrm{nrd}(x)$ which is not of the form $r\cdot y$ with $y\in\Lambda$; there is $x\in\Lambda$ with $r\nmid\mathrm{nrd}(x)$; and for $x,x'\in\Lambda$ with $r\mid\mathrm{nrd}(x)$ and $r\mid\mathrm{nrd}(x')$ the product $xx'$ lies in $r\Lambda$. Secondly, every $\mathbb{Z}$-submodule $J\le\Lambda$ with $r\cdot y\in J$ for all $y\in\Lambda$ and $mx\in J$ for all $m\in\Lambda$, $x\in J$, has either $J=r\Lambda$ (membership in $J$ equivalent to being $r\cdot y$ for some $y\in\Lambda$), or $J=\mathfrak{P}_r$ (membership in $J$ equivalent to lying in $\Lambda$ with $r\mid\mathrm{nrd}$), or $J=\Lambda$.
--
--   This is the classical description of the lattice of left $\Lambda$-ideals between $r\Lambda$ and $\Lambda$ at a prime $r$ where the indefinite quaternion algebra ramifies: the quotient $\Lambda/r\Lambda$ is uniserial, with unique intermediate ideal the maximal ideal $\mathfrak{P}_r$ of elements of reduced norm divisible by $r$, and $\mathfrak{P}_r^2\subseteq r\Lambda$. It is used in the Čerednik–Drinfeld part of the development to establish uniqueness of the Hecke (Atkin–Lehner) neighbour of a fake elliptic curve at a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq.lean

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

theorem QuaternionAlgebra.IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :

    ((∀ m ∈ Λ, ∀ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → ∃ n : ℤ, nrd (m * x) = (r : ℚ) * n) ∧
      (∀ y ∈ Λ, ∃ n : ℤ, nrd ((r : ℤ) • y) = (r : ℚ) * n) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ ¬ ∃ y ∈ Λ, x = (r : ℤ) • y) ∧
      (∃ x ∈ Λ, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∧

      (∀ x ∈ Λ, ∀ x' ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → (∃ n : ℤ, nrd x' = (r : ℚ) * n) →
        ∃ y ∈ Λ, x * x' = (r : ℤ) • y)) ∧

    ∀ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ → (∀ y ∈ Λ, (r : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      (∀ x, x ∈ J ↔ ∃ y ∈ Λ, x = (r : ℤ) • y) ∨
      (∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∨
      J = Λ := by sorry
