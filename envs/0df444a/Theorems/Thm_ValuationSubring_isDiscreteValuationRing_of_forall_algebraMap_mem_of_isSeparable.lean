-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
-- name    : ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b3449652-ba9b-546a-ba5d-4429ecc9340e
-- title:
--   Valuation subrings over a DVR in finite separable extensions
-- statement:
--   Let $C$ be a commutative domain which is a discrete valuation ring, let $K$ be a field equipped with a $C$-algebra structure making it a fraction field of $C$, and let $F$ be a field which is an algebra over both $K$ and $C$, compatibly (the scalar tower condition for $C$, $K$, $F$), finite-dimensional over $K$ and separable over $K$. Let $B$ be a valuation subring of $F$, and assume that $B$ lies over $C$ in the following two senses: the image of every $c \in C$ under the structure map $C \to F$ lies in $B$; and such an image lies in `B.nonunits`, the set of non-units of $B$ (the elements of $F$ whose $B$-valuation is $<1$, that is, the maximal ideal of $B$), precisely when $c$ belongs to the maximal ideal of the local ring $C$. The conclusion is that the ring $B$ is itself a discrete valuation ring, i.e. a local principal ideal domain that is not a field.
--
--   This is the classical statement that an extension of a discrete valuation from $K$ to a finite separable extension $F$ is again discrete, in the form: a valuation subring of $F$ lying over a discrete valuation ring of $K$ is a discrete valuation ring. It is used in the construction of valuation subrings with prescribed residue behaviour on a smooth curve of relative dimension one over a discrete valuation ring, via [`AlgebraicCurve.exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime`](thm.html#AlgebraicCurve.exists_valuationSubring_residue_of_smoothOfRelativeDimension_one_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (B : ValuationSubring F) (hCB : ∀ c : C, algebraMap C F c ∈ B)
    (hCBmax : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C) :
    IsDiscreteValuationRing ↥B := by sorry
