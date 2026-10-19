-- Prove2me | Theorems.Thm_TypeDensity_member_coefficient_measure_map_product_coordinates
-- name    : TypeDensity.member_coefficient_measure_map_product_coordinates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:35.601087+00:00
-- url     : https://prove2.me/theorems/6adb0c39-ca22-44cd-a938-acf2ab0830d6
-- title:
--   A measurable linear isomorphism onto the product of child coordinate spaces maps the parent coefficient measure to the product of child coefficient measures.
-- statement:
--   A measurable linear isomorphism onto the product of child coordinate spaces maps the parent coefficient measure to the product of child coefficient measures.
-- source:
--   TypeDensity/Measure/MemberCharts.lean#L89-L122

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Theorems.Thm_TypeDensity_coefficient_space_strict_instances
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

theorem TypeDensity.member_coefficient_measure_map_product_coordinates (m : ConcreteMember)
    (c : m.toMeasured.cellIndex) (mc : m.toMeasured.childIdx c → ConcreteMember)
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    (ρ : (Fin m.toMeasured.s.degree → m.toMeasured.O) ≃ₗ[m.toMeasured.O]
      (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O))
    (hρ : Measurable ρ) :
    MeasureTheory.Measure.map ρ (coefficientMeasure m.toMeasured.O m.toMeasured.s.degree) =
      MeasureTheory.Measure.pi
      (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) := by sorry
