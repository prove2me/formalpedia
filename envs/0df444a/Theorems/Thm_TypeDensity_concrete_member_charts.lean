-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_charts
-- name    : TypeDensity.concrete_member_charts
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:29.375015+00:00
-- url     : https://prove2.me/theorems/a49b0fd3-7974-439f-8b9a-c775593cbef7
-- title:
--   Each chart of the atlas of a concrete member is an injective measurable map onto its residue cell.
-- statement:
--   Each chart of the atlas of a concrete member is an injective measurable map onto its residue cell.
-- source:
--   TypeDensity/Recursion/Members.lean#L791-L806

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
import Theorems.Thm_TypeDensity_IdealChart_isDivisionChart
import Theorems.Thm_TypeDensity_coordinate_ideal_cell_bijection
import Theorems.Thm_TypeDensity_concrete_member_division_module_isAdicComplete
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

theorem TypeDensity.concrete_member_charts (m : ConcreteMember) (i : m.atlas.ι) :
    Function.Injective (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) ∧ Set.range
      (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) = residueIdealCell
      (algebraMap m.O m.R m.S.pi) (m.atlas.chart i).f ∧ @Measurable (Fin m.s.degree → m.O)
      (Ideal m.R) inferInstance (idealChartSigma m.O m.R m.S.pi)
      (coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b) := by sorry
