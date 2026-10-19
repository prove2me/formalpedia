-- Prove2me | Theorems.Thm_TypeDensity_overlap_point_residue_field_equiv
-- name    : TypeDensity.overlap_point_residue_field_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:31.876547+00:00
-- url     : https://prove2.me/theorems/4222f89a-764d-4bf3-880a-28599ad6f37a
-- title:
--   At a maximal ideal of the overlap on the exceptional divisor, both charts have the same residue field as the overlap, and hence the same residue length over `R`.
-- statement:
--   At a maximal ideal of the overlap on the exceptional divisor, both charts have the same residue field as the overlap, and hence the same residue length over `R`.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L850-L890

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
import Theorems.Thm_TypeDensity_blowup_overlap_isLocalization_right
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal_right
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.overlap_point_residue_field_equiv (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (beta : BlowupRestriction R t x)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈ Q) :
    (∃ φ : (BlowupChart R t x ⧸ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) ≃+*
      (BlowupOverlap R t x ⧸ Q), ∀ a : BlowupChart R t x,
      φ (Ideal.Quotient.mk (Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) a) =
      Ideal.Quotient.mk Q ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) a)) ∧
    (∃ ψ : (BlowupChart R x t ⧸ Q.comap beta.right.toRingHom) ≃+* (BlowupOverlap R t x ⧸ Q),
      ∀ b : BlowupChart R x t, ψ (Ideal.Quotient.mk (Q.comap beta.right.toRingHom) b) =
      Ideal.Quotient.mk Q (beta.right b)) ∧ Module.length R
    (BlowupChart R t x ⧸ Q.comap (algebraMap (BlowupChart R t x) (BlowupOverlap R t x))) =
    Module.length R (BlowupChart R x t ⧸ Q.comap beta.right.toRingHom) := by sorry
