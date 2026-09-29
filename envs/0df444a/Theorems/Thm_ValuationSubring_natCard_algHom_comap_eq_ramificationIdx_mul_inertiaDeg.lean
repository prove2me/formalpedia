-- Prove2me | Theorems.Thm_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
-- name    : ValuationSubring.natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/4ceb85a9-3a9f-5d20-b182-a392e47c55dd
-- title:
--   Embeddings inducing a given valuation ring number ef
-- statement:
--   Let $C$ be a discrete valuation ring (a commutative domain), let $K$ be a field that is a fraction field of $C$, and let $L$ be an algebraically closed field which is an algebra over both $C$ and $K$, compatibly (scalar tower), and which is algebraic over $K$. Let $A$ be a valuation subring of $L$ such that $\mathrm{algebraMap}\,C\,L\,c \in A$ for every $c \in C$, and such that for every $c \in C$ the resulting element of $A$ lies in the maximal ideal of $A$ precisely when $c$ lies in the maximal ideal of $C$. Let $\kappa$ be a field which is an algebra over $K$ and over $C$ compatibly, finite-dimensional and separable over $K$, and let $B$ be a valuation subring of $\kappa$ satisfying the same two conditions with respect to $C$: it contains the image of $C$, and an element $\mathrm{algebraMap}\,C\,\kappa\,c$ lies in the maximal ideal of $B$ exactly when $c$ lies in the maximal ideal of $C$. The assertion is twofold: the type of $K$-algebra homomorphisms $\sigma : \kappa \to L$ whose comap $A.\mathrm{comap}\,\sigma$ (the pullback of $A$ along $\sigma$ viewed as a ring homomorphism) equals $B$ is finite, and its cardinality equals the product of the ramification index `Ideal.ramificationIdx'` and the inertia degree `Ideal.inertiaDeg'` of the maximal ideal of $C$ at the maximal ideal of $B$, computed for the $C$-algebra structure on $B$ obtained by restricting $\mathrm{algebraMap}\,C\,\kappa$ to $B$.
--
--   This is the local decomposition-theoretic count: the $K$-embeddings of a finite separable extension $\kappa$ into an algebraic closure which induce a prescribed valuation ring $B$ on $\kappa$ form an orbit of size $e(B\mid C)\,f(B\mid C)$, the stabiliser form of the relation $\sum_i e_i f_i = [\kappa : K]$. It is used by [`IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal`](thm.html#IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal) in the counting of points over a local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra C L] [Algebra K L] [IsScalarTower C K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hCA : ∀ c : C, algebraMap C L c ∈ A)
    (hCAmax : ∀ c : C, (⟨algebraMap C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal C)
    (κ : Type*) [Field κ] [Algebra K κ] [Algebra C κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ]
    (B : ValuationSubring κ) (hCB : ∀ c : C, algebraMap C κ c ∈ B)
    (hCBmax : ∀ c : C, (⟨algebraMap C κ c, hCB c⟩ : ↥B) ∈ maximalIdeal ↥B ↔ c ∈ maximalIdeal C) :
    Finite {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} ∧
    Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} =
      (letI : Algebra C ↥B := ((algebraMap C κ).codRestrict B hCB).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B) * (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B)) := by sorry
