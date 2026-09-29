-- Prove2me | Theorems.Thm_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
-- name    : Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/cc786c67-4592-554c-9e49-0429d531a0df
-- title:
--   Additivity of dim_k Hom_Δ(N,-) on short exact sequences
-- statement:
--   Let $k$ be a field and $\Delta$ a finite group whose order, viewed in $k$ via the natural map, is a unit. Let $VN, VA, VB, VC$ be $k$-vector spaces, with $VN$ and $VB$ finite-dimensional, and let $N, A, B, C$ be representations of $\Delta$ on them, i.e. homomorphisms from $\Delta$ into the respective groups of $k$-linear automorphisms. Let $f : VA \to VB$ and $g : VB \to VC$ be $k$-linear maps that are $\Delta$-equivariant in the sense that $f \circ A(d) = B(d) \circ f$ and $g \circ B(d) = C(d) \circ g$ for every $d \in \Delta$, and assume $f$ is injective, $g$ is surjective, and the pair is exact at $VB$ (the kernel of $g$ equals the image of $f$, in Mathlib's `Function.Exact` form). Then the space of $\Delta$-invariants of the representation `N.linHom B` on $\mathrm{Hom}_k(VN, VB)$ satisfies $$\dim_k (N.\mathrm{linHom}\,B)^{\Delta} = \dim_k (N.\mathrm{linHom}\,A)^{\Delta} + \dim_k (N.\mathrm{linHom}\,C)^{\Delta},$$ the invariants of the conjugation action on $\mathrm{Hom}_k$ being exactly the $\Delta$-equivariant maps, so that this reads $\dim_k \mathrm{Hom}_\Delta(N,B) = \dim_k \mathrm{Hom}_\Delta(N,A) + \dim_k \mathrm{Hom}_\Delta(N,C)$.
--
--   This is the exactness of $\mathrm{Hom}_\Delta(N,-)$ in the semisimple situation where $|\Delta|$ is invertible in $k$ (Maschke's theorem in dimension-counting form). It is used in the computation of invariants of $k$-linear homomorphism spaces in the local analysis of $K^\times/(K^\times)^{p^n}$ as an $\mathbb{F}_p[\Delta]$-module, via [`IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq`](thm.html#IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq), and in the corresponding statement for short exact sequences in `Rep`, [`Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime`](thm.html#Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {VN VA VB VC : Type*} [AddCommGroup VN] [Module k VN] [AddCommGroup VA] [Module k VA]
    [AddCommGroup VB] [Module k VB] [AddCommGroup VC] [Module k VC]
    [FiniteDimensional k VN] [FiniteDimensional k VB]
    (N : Representation k Δ VN) (A : Representation k Δ VA) (B : Representation k Δ VB) (C : Representation k Δ VC)
    (f : VA →ₗ[k] VB) (g : VB →ₗ[k] VC) (hf : ∀ d, f ∘ₗ A d = B d ∘ₗ f) (hg : ∀ d, g ∘ₗ B d = C d ∘ₗ g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    finrank k (N.linHom B).invariants = finrank k (N.linHom A).invariants + finrank k (N.linHom C).invariants := by sorry
