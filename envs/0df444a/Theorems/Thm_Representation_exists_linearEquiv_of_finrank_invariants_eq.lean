-- Prove2me | Theorems.Thm_Representation_exists_linearEquiv_of_finrank_invariants_eq
-- name    : Representation.exists_linearEquiv_of_finrank_invariants_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/9e1a8c27-f714-585d-a109-68a0875afddb
-- title:
--   Rational representations of a cyclic group determined by invariant dimensions
-- statement:
--   Let $G$ be a finite cyclic group and let $V$, $W$ be finite-dimensional $\mathbb{Q}$-vector spaces carrying $\mathbb{Q}$-linear representations $\rho \colon G \to \mathrm{GL}(V)$ and $\tau \colon G \to \mathrm{GL}(W)$. Assume that for every subgroup $H \le G$ the spaces of $H$-invariants have the same dimension, that is, $\dim_{\mathbb{Q}} V^{H} = \dim_{\mathbb{Q}} W^{H}$, where $V^{H}$ denotes the invariants of the representation obtained by composing $\rho$ with the inclusion $H \hookrightarrow G$, and likewise for $W$ and $\tau$. Then there exists a $\mathbb{Q}$-linear isomorphism $e \colon V \to W$ which is $G$-equivariant in the explicit sense that $e(\rho(g)v) = \tau(g)(e(v))$ for all $g \in G$ and all $v \in V$. The equivariance is stated pointwise for the underlying $\mathbb{Q}$-linear equivalence rather than as an isomorphism of $G$-representations in a fixed category of representations.
--
--   This is the statement that a finite-dimensional rational representation of a finite cyclic group is determined up to isomorphism by the dimensions of the fixed subspaces of all subgroups (equivalently, by its character, via the dimensions $\dim V^{H}$). It is used in the construction of injective homomorphisms of representations with finite-index image, through [`Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq`](thm.html#Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_linearEquiv_of_finrank_invariants_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum

theorem Representation.exists_linearEquiv_of_finrank_invariants_eq {G V W : Type*} [Group G] [Fintype G] [IsCyclic G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (h : ∀ H : Subgroup G, Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) =
      Module.finrank ℚ (Representation.invariants (τ.comp H.subtype))) :
    ∃ e : V ≃ₗ[ℚ] W, ∀ (g : G) (v : V), e (ρ g v) = τ g (e v) := by sorry
