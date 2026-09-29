-- Prove2me | Theorems.Thm_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective
-- name    : UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/a3bdc639-f842-57ef-a0aa-3c3fa7d91408
-- title:
--   Unit cocycles on basic opens of a UFD are coboundaries
-- statement:
--   Let $B$ be a domain which is a unique factorisation monoid, $K$ a field and $\varphi\colon B \to K$ an injective ring homomorphism. Let $\iota$ be a type, $b\colon \iota \to B$ a family of elements of $B$ and $u\colon \iota \to \iota \to K$ a family of elements of $K$ subject to three conditions, all of which are imposed only at indices where the corresponding $b$'s are nonzero: for all $i,j$ with $b_i \neq 0$ and $b_j \neq 0$ there exist $n \in \mathbb{N}$ and $x \in B$ with $u_{ij}\,\varphi(b_i b_j)^n = \varphi(x)$; $u_{ii} = 1$ whenever $b_i \neq 0$; and $u_{ij} u_{jk} = u_{ik}$ whenever $b_i, b_j, b_k \neq 0$. The conclusion asserts the existence of a family $h\colon \iota \to K$ such that, first, for every $i$ with $b_i \neq 0$ one has $h_i \neq 0$ together with natural numbers and elements of $B$ exhibiting $h_i\,\varphi(b_i)^n = \varphi(x)$ and $h_i^{-1}\varphi(b_i)^{m} = \varphi(y)$ for some $n, m, x, y$; and second, $u_{ij} h_j = h_i$ for all $i,j$ with $b_i \neq 0$ and $b_j \neq 0$. No condition is imposed on $h_i$ at indices with $b_i = 0$.
--
--   In geometric terms this is the vanishing of the Čech $H^1$ of the sheaf of units for a covering of an open subset of $\operatorname{Spec} B$ by basic open sets $D(b_i)$, $B$ a unique factorisation domain: the $u_{ij}$, regular and invertible on $D(b_i b_j)$ after clearing a power of $b_i b_j$, are split by units $h_i$ on $D(b_i)$. It is the algebraic core of the statement that an invertible module on such an open subscheme, here [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid), is isomorphic to the unit object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
    {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {K : Type*} [Field K] (φ : B →+* K) (hφ : Function.Injective φ)
    {ι : Type*} (b : ι → B) (u : ι → ι → K)
    (hreg : ∀ i j, b i ≠ 0 → b j ≠ 0 → ∃ (n : ℕ) (x : B), u i j * φ (b i * b j) ^ n = φ x)
    (hrefl : ∀ i, b i ≠ 0 → u i i = 1)
    (hcocycle : ∀ i j k, b i ≠ 0 → b j ≠ 0 → b k ≠ 0 → u i j * u j k = u i k) :
    ∃ h : ι → K, (∀ i, b i ≠ 0 →
        h i ≠ 0 ∧ (∃ (n : ℕ) (x : B), h i * φ (b i) ^ n = φ x) ∧
          (∃ (n : ℕ) (y : B), (h i)⁻¹ * φ (b i) ^ n = φ y)) ∧
      ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j * h j = h i := by sorry
