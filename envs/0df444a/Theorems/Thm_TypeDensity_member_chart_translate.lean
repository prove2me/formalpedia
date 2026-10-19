-- Prove2me | Theorems.Thm_TypeDensity_member_chart_translate
-- name    : TypeDensity.member_chart_translate
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:16.077848+00:00
-- url     : https://prove2.me/theorems/97930b6f-172c-45fb-b7b3-b5c938b53187
-- title:
--   Translating chart coordinates by `z₀` recenters the generator at `f + π Σ z₀ᵢ bᵢ`, maps cosets to translated cosets, and preserves the coefficient measure and measurability.
-- statement:
--   Translating chart coordinates by `z₀` recenters the generator at `f + π Σ z₀ᵢ bᵢ`, maps cosets to translated cosets, and preserves the coefficient measure and measurability.
-- source:
--   TypeDensity/Measure/MemberCharts.lean#L42-L79

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
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
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

theorem TypeDensity.member_chart_translate (m : ConcreteMember) (f : m.toMeasured.R)
    (b : Fin m.toMeasured.s.degree → m.toMeasured.R) (Mlev : ℕ)
    (z₀ : Fin m.toMeasured.s.degree → m.toMeasured.O) :
    (∀ z, coordinateIdeal m.toMeasured.S.pi f b (z₀ + z) =
      coordinateIdeal m.toMeasured.S.pi (f + m.toMeasured.S.pi • coordinateLift b z₀) b z) ∧
      coordinateCoset m.toMeasured.S.pi Mlev z₀ =
      (fun z => z₀ + z) '' Set.range (coordinateScale m.toMeasured.S.pi Mlev) ∧
        ∀ A : Set (Fin m.toMeasured.s.degree → m.toMeasured.O),
        coefficientMeasure m.toMeasured.O m.toMeasured.s.degree ((fun z => z₀ + z) '' A) =
        coefficientMeasure m.toMeasured.O m.toMeasured.s.degree A ∧
        (MeasurableSet A → MeasurableSet ((fun z => z₀ + z) '' A)) := by sorry
