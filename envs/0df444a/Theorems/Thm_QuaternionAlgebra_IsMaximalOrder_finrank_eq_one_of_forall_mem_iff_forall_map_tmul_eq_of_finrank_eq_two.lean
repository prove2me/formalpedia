-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two
-- name    : QuaternionAlgebra.IsMaximalOrder.finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/e3575a11-cf5b-5590-8f65-08e44e2855f1
-- title:
--   Equivariant tensors for a maximal quaternion order form a line
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra, and let $q,q'$ be primes such that the predicate `IsIndefiniteRamifiedExactlyAt` holds for $a,b,q,q'$, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing it equals it. Let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$, let $k$ be a field of characteristic $\ell$, and let $V$, $W$ be finite-dimensional $k$-vector spaces with $\dim_k V=\dim_k W=2$. Let $\theta:\Lambda\to\operatorname{End}_k(V)$ be additive, send $1$ to $1$ and satisfy $\theta(xy)=\theta(x)\theta(y)$ whenever $xy\in\Lambda$, and let $\rho:\Lambda\to\operatorname{End}_k(W)$ be additive, send $1$ to $1$ and satisfy the opposite rule $\rho(xy)=\rho(y)\rho(x)$. Let $T\subseteq V\otimes_k W$ be a $k$-subspace whose members are exactly the $\xi$ with $(\theta(x)\otimes \mathrm{id})\xi=(\mathrm{id}\otimes\rho(x))\xi$ for all $x\in\Lambda$. Then $\dim_k T=1$.
--
--   This is the Morita-equivalence count underlying the comparison of a quaternionic action on a pair of planes: away from the two ramified primes the reduction of a maximal order is a matrix algebra, and the space of tensors intertwining an action and an anti-action of it is one-dimensional. It is used in the construction of fake elliptic curves and their level structures in the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.finrank_eq_one_of_forall_mem_iff_forall_map_tmul_eq_of_finrank_eq_two
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    {k : Type*} [Field k] [CharP k ℓ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (hW : Module.finrank k W = 2)

    (θ : ↥Λ → Module.End k V)
    (hθadd : ∀ x y : ↥Λ, θ (x + y) = θ x + θ y)
    (hθone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h⟩ = 1)
    (hθmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = θ x * θ y)

    (ρ : ↥Λ → Module.End k W)
    (hρadd : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (hρone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1)
    (hρmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ y * ρ x)

    (T : Submodule k (V ⊗[k] W))
    (hT : ∀ ξ : V ⊗[k] W, ξ ∈ T ↔
      ∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : W →ₗ[k] W) ξ = TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) ξ) :
    Module.finrank k ↥T = 1 := by sorry
