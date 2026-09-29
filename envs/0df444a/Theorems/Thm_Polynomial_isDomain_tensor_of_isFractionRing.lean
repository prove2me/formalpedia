-- Prove2me | Theorems.Thm_Polynomial_isDomain_tensor_of_isFractionRing
-- name    : Polynomial.isDomain_tensor_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a7928e7c-23d5-51f2-bece-56a10d78a9bc
-- title:
--   Geometric integrality of the rational function field
-- statement:
--   Let $F_0$ be a field, $\kappa$ a commutative ring and $k$ a field. Assume $\kappa$ carries an $F_0[X]$-algebra structure making it a fraction ring of the polynomial ring $F_0[X]$, i.e. a localisation of $F_0[X]$ at its monoid of non-zero-divisors; so $\kappa$ is a copy of the rational function field $F_0(X)$. Assume further that $\kappa$ is an $F_0$-algebra in a way compatible with the above, in the sense that the $F_0$-action factors through $F_0[X]$ (an `IsScalarTower F₀ F₀[X] κ` hypothesis), and that $k$ is an $F_0$-algebra, hence a field extension of $F_0$. The conclusion is that the tensor product $\kappa \otimes_{F_0} k$, with its induced commutative ring structure, is an integral domain: it is non-trivial, has no zero divisors, and multiplication by a non-zero element is cancellative. Equivalently, $F_0(X)$ is geometrically integral over $F_0$, this being asserted for every field extension $k/F_0$ with no separability or finiteness assumption.
--
--   The statement records that the rational function field over a field stays a domain after arbitrary base field extension, i.e. that $\mathbb{A}^1$'s function field is geometrically integral. It is used by [`Subalgebra.isReduced_tensor_of_separable`](thm.html#Subalgebra.isReduced_tensor_of_separable), where reducedness established over a small base field must be propagated to every extension field of the same characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_isDomain_tensor_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped TensorProduct

universe u₁ u₂ u₃

theorem Polynomial.isDomain_tensor_of_isFractionRing
    (F₀ : Type u₁) (κ : Type u₂) (k : Type u₃) [Field F₀] [CommRing κ] [Field k]
    [Algebra F₀[X] κ] [IsFractionRing F₀[X] κ] [Algebra F₀ κ] [IsScalarTower F₀ F₀[X] κ]
    [Algebra F₀ k] : IsDomain (κ ⊗[F₀] k) := by sorry
