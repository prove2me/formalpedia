-- Prove2me | Theorems.Thm_TypeDensity_member_cell_box_measurable
-- name    : TypeDensity.member_cell_box_measurable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:10:55.358794+00:00
-- url     : https://prove2.me/theorems/4362fdb5-bfc2-4577-9865-acb422bed9a3
-- title:
--   The set of ideals in a cell whose strict transforms lie in a measurable box `Π G_j` is measurable.
-- statement:
--   The set of ideals in a cell whose strict transforms lie in a measurable box `Π G_j` is measurable.
-- source:
--   TypeDensity/Measure/MemberBoxes.lean#L489-L519

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
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
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Assembly_NullBridges
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Theorems.Thm_TypeDensity_tri_chooseTwo
import Theorems.Thm_TypeDensity_IdealChart_isDivisionChart
import Theorems.Thm_TypeDensity_common_vertical_exponent
import Theorems.Thm_TypeDensity_chart_image_measurable_chart_sigma
import Theorems.Thm_TypeDensity_member_cell_chart_box
import Theorems.Thm_TypeDensity_member_cell_chart_coset_decomposition
import Theorems.Thm_TypeDensity_concrete_member_charts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal
variable (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (mc : m.toMeasured.childIdx c → ConcreteMember)
variable [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.R]
    [∀ j, IsScalarTower m.toMeasured.O (mc j).toMeasured.O (mc j).toMeasured.R]
    (pc : ∀ j, (mc j).toMeasured.O ≃ₗ[m.toMeasured.O]
      (Fin (m.toMeasured.childDelta c j) → m.toMeasured.O))
    (hpc : ∀ j, Measurable (pc j)) (hpc' : ∀ j, Measurable (pc j).symm)
    (hcard : ∀ j, (mc j).toMeasured.q = m.toMeasured.q ^ m.toMeasured.childDelta c j)
    (hpiO : ∀ j, algebraMap m.toMeasured.O (mc j).toMeasured.O m.toMeasured.S.pi =
      (mc j).toMeasured.S.pi)
    (hdeg : ∑ j, m.toMeasured.childDelta c j * (mc j).toMeasured.s.degree = m.toMeasured.s.degree)
    (alpha : ∀ j, m.toMeasured.R →ₐ[m.toMeasured.O] (mc j).toMeasured.R)
    (e : ∀ j, (mc j).toMeasured.R) (he : ∀ j, e j = (mc j).toMeasured.S.t)
    (hvert : ∀ j, ∃ (s : ℕ) (cj : (mc j).toMeasured.R),
      algebraMap m.toMeasured.O (mc j).toMeasured.R m.toMeasured.S.pi ^ s =
      e j ^ m.toMeasured.cellDegree c * cj)
    (hbij : Set.BijOn
      (fun (J : Ideal m.toMeasured.R) (j : m.toMeasured.childIdx c) => strictTransformIdeal
      (alpha j) (e j) (m.toMeasured.cellDegree c) J) (m.toMeasured.cell c)
      (Set.pi Set.univ fun j => (mc j).toMeasured.stateSet))
    (hstrict : ∀ f : m.toMeasured.R, Ideal.span {f} ∈ m.toMeasured.cell c →
      ∃ g : (∀ j, (mc j).toMeasured.R), ∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j)
    (hindex : ∀ f : m.toMeasured.R, Ideal.span {f} ∈ m.toMeasured.cell c →
      ∀ g : (∀ j, (mc j).toMeasured.R), (∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j) →
      ∀ iota : (m.toMeasured.R ⧸ Ideal.span {f}) →ₗ[m.toMeasured.O]
      ((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}),
      (∀ h : m.toMeasured.R, iota (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (fun j => alpha j h)) → Function.Injective iota ∧
      Module.length m.toMeasured.O
      (((∀ j, (mc j).toMeasured.R) ⧸ Ideal.span {g}) ⧸ LinearMap.range iota) =
      (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞))
    (hsum : ∑ j, m.toMeasured.childDelta c j * (mc j).toMeasured.s.firstContact =
      m.toMeasured.cellDegree c)
include hcard hpiO he hbij hindex hsum
include pc hpc hpc' hdeg hvert hstrict

theorem TypeDensity.member_cell_box_measurable :
    (letI : ∀ j, MeasurableSpace (Ideal (mc j).toMeasured.R) :=
      fun j => (mc j).toMeasured.measurableSpaceIdeal;
      letI : MeasurableSpace (Ideal (m.toMeasured.R)) := m.toMeasured.measurableSpaceIdeal;
      ∀ (G : ∀ j, Set (Ideal (mc j).toMeasured.R)), (∀ j, MeasurableSet (G j)) →
      MeasurableSet (m.toMeasured.cell c ∩ (fun (J : Ideal (m.toMeasured.R)) (j : (m.toMeasured.childIdx c)) =>
        strictTransformIdeal (alpha j) (e j) (m.toMeasured.cellDegree c) J) ⁻¹' Set.pi Set.univ G)) := by sorry
