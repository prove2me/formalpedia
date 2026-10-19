-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_division_chart_measure
-- name    : TypeDensity.concrete_member_division_chart_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:07.533982+00:00
-- url     : https://prove2.me/theorems/97d5395d-4ea1-4a62-ace0-cd00def77889
-- title:
--   A division chart centred at a generator of an ideal of the state set is injective, lands in the state set, and scales the coefficient measure by `q^(-deg s)`.
-- statement:
--   A division chart centred at a generator of an ideal of the state set is injective, lands in the state set, and scales the coefficient measure by `q^(-deg s)`.
-- source:
--   TypeDensity/Recursion/Members.lean#L999-L1076

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
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_principal_ideal_image
import Theorems.Thm_TypeDensity_IdealChart_isDivisionChart
import Theorems.Thm_TypeDensity_coordinate_ideal_in_residue_cell
import Theorems.Thm_TypeDensity_division_chart_same_cell_recenter
import Theorems.Thm_TypeDensity_chart_image_measurable_chart_sigma
import Theorems.Thm_TypeDensity_ideal_chart_pushforward_independent
import Theorems.Thm_TypeDensity_coordinate_ideal_injective
import Theorems.Thm_TypeDensity_concrete_member_division_module_isAdicComplete
import Theorems.Thm_TypeDensity_concrete_member_charts
import Theorems.Thm_TypeDensity_concrete_member_state_generator_regular
import Theorems.Thm_TypeDensity_coordinate_ideal_measurable_chart_sigma
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
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.concrete_member_division_chart_measure (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) (bc : Fin m.toMeasured.s.degree → m.toMeasured.R)
    (E : m.toMeasured.R ≃ₗ[m.toMeasured.O] ((Fin m.toMeasured.s.degree → m.toMeasured.O) ×
    m.toMeasured.R)) (hE : ∀ w, E.symm w = divisionMap g bc w) :
    Function.Injective (coordinateIdeal m.toMeasured.S.pi g bc) ∧ Set.range
      (coordinateIdeal m.toMeasured.S.pi g bc) ⊆ m.toMeasured.stateSet ∧ ∀ S : Set
      (Fin m.toMeasured.s.degree → m.toMeasured.O), MeasurableSet S → m.toMeasured.μ
      (coordinateIdeal m.toMeasured.S.pi g bc '' S) = (m.toMeasured.q : ℝ≥0∞)⁻¹ ^
      m.toMeasured.s.degree * coefficientMeasure m.toMeasured.O m.toMeasured.s.degree S := by sorry
