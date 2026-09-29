-- Prove2me | Theorems.Thm_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
-- name    : RingHom.exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/1f2eb934-5e86-5f4a-96b2-a240674c2433
-- title:
--   Casimir element with unit product modulo ℓ
-- statement:
--   Let $R$ be a ring whose underlying additive group is a free $\mathbb{Z}$-module of finite rank, let $\ell$ be a prime, and let $n$ be a non-empty finite index type. Let $\psi \colon R \to M_n(\mathbb{Z}/\ell)$ be a surjective ring homomorphism whose kernel is exactly $\ell R$, in the sense that for every $x \in R$ one has $\psi(x) = 0$ if and only if $x = \ell y$ for some $y \in R$. Suppose given an element $c_0$ of the ring $R \otimes_{\mathbb{Z}} R$ which is non-zero and satisfies the Casimir condition $(x \otimes 1)\, c_0 = c_0\, (1 \otimes x)$ for all $x \in R$. The conclusion is that there exists $c \in R \otimes_{\mathbb{Z}} R$ satisfying the same Casimir condition $(x \otimes 1)\, c = c\, (1 \otimes x)$ for all $x \in R$, and such that the image under $\psi$ of the multiplication map $\mathrm{LinearMap.mul}\ \mathbb{Z}\ R$ applied to $c$ — that is, $\psi\bigl(\sum_i u_i v_i\bigr)$ for any presentation $c = \sum_i u_i \otimes v_i$ — equals the identity matrix $1 \in M_n(\mathbb{Z}/\ell)$. Thus an arbitrary non-zero Casimir element can be replaced by one whose collapsed product is a unit after reduction modulo $\ell$.
--
--   This is the arithmetic normalisation step underlying the separability (Azumaya) property of a ring that reduces modulo $\ell$ onto a matrix algebra over $\mathbb{F}_\ell$: the Casimir element is rescaled so that its collapsed product becomes the identity in the reduction. It is used in the construction of separability elements for maximal orders in indefinite quaternion algebras ramified exactly at a prescribed set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem RingHom.exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
    {R : Type v} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (ℓ : ℕ) [Fact ℓ.Prime] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c₀ : R ⊗[ℤ] R) (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ = c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0) :
    ∃ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) ∧
      ψ (LinearMap.mul' ℤ R c) = 1 := by sorry
