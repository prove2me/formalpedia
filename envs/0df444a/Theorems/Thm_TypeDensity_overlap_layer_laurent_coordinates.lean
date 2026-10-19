-- Prove2me | Theorems.Thm_TypeDensity_overlap_layer_laurent_coordinates
-- name    : TypeDensity.overlap_layer_laurent_coordinates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:36.993045+00:00
-- url     : https://prove2.me/theorems/ba27b26b-2317-49e5-8d31-89a78920bc14
-- title:
--   Each exceptional layer of the overlap is `R`-linearly isomorphic to the Laurent polynomial ring `(R/(t,x))[Z, Z⁻¹]`, the monomial `r Z^ℓ` corresponding to the layer class of `r · z^ℓ`.
-- statement:
--   Each exceptional layer of the overlap is `R`-linearly isomorphic to the Laurent polynomial ring `(R/(t,x))[Z, Z⁻¹]`, the monomial `r Z^ℓ` corresponding to the layer class of `r · z^ℓ`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L51-L134

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
import Theorems.Thm_TypeDensity_exceptional_overlap_is_laurent_line
import Theorems.Thm_TypeDensity_principal_layer_quotient_equiv
import Theorems.Thm_TypeDensity_localization_principal_quotient_commute
import Theorems.Thm_TypeDensity_nonzerodivisor_survives_localization
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.overlap_layer_laurent_coordinates (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (j : ℕ) :
    ∃ L : LaurentPolynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupOverlap R t x)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j, ∀ r : R,
    ∀ ell : ℤ, (L (LaurentPolynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) *
      LaurentPolynomial.T ell)).val = principalLayerMap (BlowupOverlap R t x)
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t)) j
    ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x r) * selfZPow
      (chartSlope R t x) (BlowupOverlap R t x) ell) := by sorry
