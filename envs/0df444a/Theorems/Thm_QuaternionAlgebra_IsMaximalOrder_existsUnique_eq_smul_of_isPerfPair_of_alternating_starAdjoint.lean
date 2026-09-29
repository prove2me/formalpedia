-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint
-- name    : QuaternionAlgebra.IsMaximalOrder.existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/1978d38c-408a-5980-a166-280c8cc4ea4b
-- title:
--   Uniqueness of ⋆-alternating forms up to scalar
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, spans $B$ over $\mathbb{Q}$ and is finitely generated, and any order containing $\Lambda$ equals $\Lambda$. Let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\star:\Lambda\to\Lambda$ be a map with $\mu\,x^{\star}=\bar{x}\,\mu$ for all $x\in\Lambda$, where $\bar{\;}$ is quaternion conjugation. Let $R$ be a commutative domain of characteristic $0$, $M$ an $R$-module, and $\rho$ a map from $\Lambda$ to $R$-endomorphisms of $M$ which is additive, sends $1$ to the identity and satisfies $\rho(xy)=\rho(x)\circ\rho(y)$. Assume given a $\mathbb{Z}$-basis $(x_i)_{i\in\iota}$ of $\Lambda$, a vector $e\in M$ and an $R$-basis $(m_i)_{i\in\iota}$ of $M$ with $m_i=\rho(x_i)e$. Let $E_0,E:M\times M\to R$ be $R$-bilinear forms, each alternating ($E_0(m,m)=0$, $E(m,m)=0$) and $\star$-adjoint ($E_0(\rho(x)m,n)=E_0(m,\rho(x^{\star})n)$, and likewise for $E$), and suppose moreover that $E_0$ is a perfect pairing. Then there is a unique $r\in R$ with $E=r\,E_0$.
--
--   This is the uniqueness, up to a scalar, of the polarisation form on a rank-one module over a maximal order in an indefinite quaternion algebra ramified exactly at two primes: a perfect alternating $\star$-adjoint form generates all alternating $\star$-adjoint forms. It is used in the Čerednik–Drinfeld part of the construction, in the compatibility of Rosati involutions for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u v w

theorem QuaternionAlgebra.IsMaximalOrder.existsUnique_eq_smul_of_isPerfPair_of_alternating_starAdjoint
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
    (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)
    (E₀ : M →ₗ[R] M →ₗ[R] R) (h₀alt : ∀ m : M, E₀ m m = 0)
    (h₀star : ∀ (x : ↥Λ) (m n : M), E₀ (ρ x m) n = E₀ m (ρ (star x) n))
    (hperf : E₀.IsPerfPair)
    (E : M →ₗ[R] M →ₗ[R] R) (halt : ∀ m : M, E m m = 0)
    (hstarE : ∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) :
    ∃! r : R, E = r • E₀ := by sorry
