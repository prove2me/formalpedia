-- Prove2me | Theorems.Thm_TypeDensity_member_product_chart_pushforward
-- name    : TypeDensity.member_product_chart_pushforward
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:53:39.307625+00:00
-- url     : https://prove2.me/theorems/cdf76de6-f5e4-441c-8e8e-0c5eb0073991
-- title:
--   The product of child coordinate-ideal maps is a measurable embedding, and pushes the product state measure back to `Π_j q_j^(-deg_j)` times the product coefficient measure.
-- statement:
--   The product of child coordinate-ideal maps is a measurable embedding, and pushes the product state measure back to `Π_j q_j^(-deg_j)` times the product coefficient measure.
-- source:
--   TypeDensity/Measure/MemberCharts.lean#L369-L430

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
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_measurableEmbedding_pi
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_concrete_member_division_module_isAdicComplete
import Theorems.Thm_TypeDensity_concrete_member_measure_finite_support
import Theorems.Thm_TypeDensity_concrete_member_state_generator_regular
import Theorems.Thm_TypeDensity_concrete_member_division_chart_measure
import Theorems.Thm_TypeDensity_coordinate_ideal_measurableEmbedding
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

theorem TypeDensity.member_product_chart_pushforward (ι : Type) [Fintype ι] (mc : ι → ConcreteMember)
    (g : ∀ j, (mc j).toMeasured.R) (hg : ∀ j, Ideal.span {g j} ∈ (mc j).toMeasured.stateSet)
    (bc' : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.R)
    (E' : ∀ j, (mc j).toMeasured.R ≃ₗ[(mc j).toMeasured.O]
      ((Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) × (mc j).toMeasured.R))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w) :
    (letI : ∀ j, MeasurableSpace (Ideal (mc j).toMeasured.R) :=
      fun j => (mc j).toMeasured.measurableSpaceIdeal; MeasurableEmbedding
        (fun (w : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) (j : ι)
        => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)) ∧
        ∀ Y : Set (∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O), MeasurableSet Y →
        MeasureTheory.Measure.pi (fun j => (mc j).toMeasured.μ)
        ((fun (w : ∀ j, Fin (mc j).toMeasured.s.degree → (mc j).toMeasured.O) (j : ι)
        => coordinateIdeal (mc j).toMeasured.S.pi (g j) (bc' j) (w j)) '' Y) =
        (∏ j, ((mc j).toMeasured.q : ℝ≥0∞)⁻¹ ^ (mc j).toMeasured.s.degree) *
        MeasureTheory.Measure.pi
        (fun j => coefficientMeasure (mc j).toMeasured.O (mc j).toMeasured.s.degree) Y) := by sorry
