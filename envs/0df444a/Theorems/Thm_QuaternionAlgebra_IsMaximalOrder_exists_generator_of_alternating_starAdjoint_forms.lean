-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_of_alternating_starAdjoint_forms
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_generator_of_alternating_starAdjoint_forms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/0e8d4b30-8bc8-57cf-80cb-85464ab51490
-- title:
--   Uniqueness of ⋆-alternating forms on a rank-one module
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies the project's condition `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is the largest such submodule containing it. Let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be any map with $\mu\,\mathrm{star}(x)=\bar{x}\,\mu$ for all $x$. Let $R$ be a characteristic-zero commutative domain and $M$ an $R$-module, equipped with a map $\rho$ from $\Lambda$ to $R$-linear endomorphisms of $M$ that sends $1$ to the identity, is additive, and satisfies $\rho(xy)=\rho(x)\circ\rho(y)$. Assume $M$ is free of rank one over $\Lambda\otimes R$ in the concrete sense that for some $\mathbb{Z}$-basis $(x_i)_{i\in\iota}$ of $\Lambda$ and some $e\in M$, the family $(\rho(x_i)e)_{i\in\iota}$ is an $R$-basis of $M$. Then there is an $R$-bilinear form $E_0:M\to M\to R$ with $E_0(m,m)=0$ and $E_0(\rho(x)m,n)=E_0(m,\rho(\mathrm{star}(x))n)$ for all $x\in\Lambda$, $m,n\in M$, such that every bilinear form $E$ with these two properties is $r\cdot E_0$ for a unique $r\in R$.
--
--   This says that the $\star$-alternating $R$-bilinear forms on a rank-one module over $\Lambda\otimes R$ constitute a free $R$-module of rank one, the algebraic input for normalising a Rosati-compatible pairing on fake elliptic curves with quaternionic multiplication. It is used in the Čerednik–Drinfel'd part of the development, both for the perfectness statement for such forms and for the triviality of the kernel of the resulting map on tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_generator_of_alternating_starAdjoint_forms.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u v w

theorem QuaternionAlgebra.IsMaximalOrder.exists_generator_of_alternating_starAdjoint_forms
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ρ : ↥Λ → (M →ₗ[R] M))
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    {ι : Type w} (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
    (hbM : ∀ i : ι, bM i = ρ (bΛ i) e) :
    ∃ E₀ : M →ₗ[R] M →ₗ[R] R,
      (∀ m : M, E₀ m m = 0) ∧ (∀ (x : ↥Λ) (m n : M), E₀ (ρ x m) n = E₀ m (ρ (star x) n)) ∧
      ∀ E : M →ₗ[R] M →ₗ[R] R, (∀ m : M, E m m = 0) →
        (∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) →
        ∃! r : R, E = r • E₀ := by sorry
