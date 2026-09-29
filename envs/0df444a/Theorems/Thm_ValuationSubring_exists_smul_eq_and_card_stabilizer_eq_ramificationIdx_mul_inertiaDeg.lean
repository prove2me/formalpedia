-- Prove2me | Theorems.Thm_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
-- name    : ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/94329401-7ed4-5a3d-92d8-974b3c43298f
-- title:
--   Conjugacy of extensions and order ef of the decomposition group
-- statement:
--   Let $C$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring in Mathlib's sense), let $K$ be a field that is a $C$-algebra and a fraction field of $C$, and let $M$ be a field equipped with compatible $K$- and $C$-algebra structures (the scalar tower $C \to K \to M$), finite-dimensional over $K$ and Galois over $K$. Let $V$ be a valuation subring of $M$ such that $\mathrm{algebraMap}\ C\ M$ maps $C$ into $V$, and such that for every $c \in C$ the image of $c$ lies in the set of non-units of $V$ exactly when $c$ lies in the maximal ideal of $C$. Two assertions are made. First, for every valuation subring $V'$ of $M$ satisfying these same two conditions with respect to $C$, there exists a $K$-algebra automorphism $g$ of $M$ with $g \bullet V' = V$; thus $\mathrm{Gal}(M/K)$ acts transitively on the valuation subrings of $M$ lying over $C$ in this sense. Second, the cardinality of the decomposition subgroup `ValuationSubring.decompositionSubgroup` of $V$ over $K$, i.e. of the stabiliser of $V$ in $M \simeq_{\mathrm{alg}[K]} M$, equals the product of the ramification index $e$ and the inertia degree $f$ of the maximal ideal of $V$ over the maximal ideal of $C$, computed for the $C$-algebra structure on $V$ obtained by restricting $\mathrm{algebraMap}\ C\ M$ to its codomain $V$.
--
--   This is the classical statement that the Galois group of a finite Galois extension $M/K$ permutes the extensions of a discrete valuation of $K$ to $M$ transitively, together with the formula $\#D_V = ef$ for the order of the decomposition group; no separability hypothesis on the residue extension is imposed. It is used in the treatment of places of algebraic curves, where it yields the factorisation of the order of a stabiliser into $e$, $f$ and the order of the corresponding stabiliser upstairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise

theorem ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal C).inertiaDeg' (maximalIdeal ↥V)) := by sorry
