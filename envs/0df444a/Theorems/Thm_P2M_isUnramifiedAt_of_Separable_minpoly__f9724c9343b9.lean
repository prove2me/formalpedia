-- Prove2me | Theorems.Thm_P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9
-- name    : P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:21.456875+00:00
-- url     : https://prove2.me/theorems/67429495-a4f9-4572-ab55-6eb5a2f28973
-- title:
--   P2 M is Unramified At of Separable minpoly  f9724c9343b9: P2 M is Unramified At of Separable minpoly  f9724c9343b9
-- statement:
--   The P2 M is Unramified At of Separable minpoly  f9724c9343b9 construction uses the P2 M is Unramified At of Separable minpoly  f9724c9343b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Unramified.lean#L142-L174
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Unramified.lean#L142-L174

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
public import Definitions.Def_FltRegular_NumberTheory_Unramified
set_option autoImplicit false
@[expose] public section
public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
open nonZeroDivisors Polynomial
attribute [local instance] Ideal.Quotient.field

theorem P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9 [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : S)
    (hx' : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by sorry

alias «isUnramifiedAt_of_Separable_minpoly'» := P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9
