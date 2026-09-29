-- Prove2me | Theorems.Thm_Representation_finrank_invariants_dual_of_isUnit_card
-- name    : Representation.finrank_invariants_dual_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7626991d-00c6-52f7-a4b2-70c4737f6920
-- title:
--   Dual representation has invariants of equal dimension
-- statement:
--   Let $k$ be a field and $\Delta$ a finite group whose order is invertible in $k$: the hypothesis is that the image of $\mathrm{card}\,\Delta$ under the canonical map $\mathbb{N} \to k$ is a unit. Let $V$ be a finite-dimensional $k$-vector space and let $\rho$ be a representation of $\Delta$ on $V$ over $k$, i.e. a monoid homomorphism from $\Delta$ to the $k$-linear endomorphisms of $V$. Write $\rho.\mathrm{dual}$ for Mathlib's contragredient representation on the dual space $\mathrm{Dual}\,k\,V$, acting on a linear form by transposing the action of the inverse group element, and write $\rho.\mathrm{invariants}$ for the $k$-submodule of vectors fixed by every $\rho(g)$. The assertion is the equality of $k$-dimensions $$\dim_k (\rho.\mathrm{dual}).\mathrm{invariants} = \dim_k \rho.\mathrm{invariants},$$ i.e. the space of $\Delta$-invariant linear forms on $V$ has the same finite rank as the space of $\Delta$-invariant vectors of $V$.
--
--   This is the standard statement, valid whenever $\#\Delta$ is invertible in the coefficient field, that taking invariants commutes with duality up to dimension, so that $h^0$ of the contragredient agrees with $h^0$ of the representation. It is used in the tame local Euler-characteristic computation, being cited by [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_dual_of_isUnit_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.finrank_invariants_dual_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants := by sorry
