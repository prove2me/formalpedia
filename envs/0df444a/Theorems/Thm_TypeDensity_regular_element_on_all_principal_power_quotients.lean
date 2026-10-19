-- Prove2me | Theorems.Thm_TypeDensity_regular_element_on_all_principal_power_quotients
-- name    : TypeDensity.regular_element_on_all_principal_power_quotients
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:44.630201+00:00
-- url     : https://prove2.me/theorems/95df3468-8f94-4b0f-9ff6-819b038e0262
-- title:
--   If `e` is a nonzerodivisor and `f` is a nonzerodivisor modulo `e`, then `f` is a nonzerodivisor modulo every power `(e)^j`.
-- statement:
--   If `e` is a nonzerodivisor and `f` is a nonzerodivisor modulo `e`, then `f` is a nonzerodivisor modulo every power `(e)^j`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L693-L725

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

theorem TypeDensity.regular_element_on_all_principal_power_quotients (A : Type) [CommRing A] (e f : A)
    (he : Function.Injective (fun a : A ↦ e*a))
    (hf : Function.Injective
      (fun a : A ⧸ Ideal.span {e} ↦ Ideal.Quotient.mk (Ideal.span {e}) f * a)) (j : ℕ) :
    Function.Injective
      (fun a : A ⧸ (Ideal.span {e})^j ↦ Ideal.Quotient.mk ((Ideal.span {e})^j) f * a) := by sorry
