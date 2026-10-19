-- Prove2me | Theorems.Thm_TypeDensity_member_cell_chart_coset_decomposition
-- name    : TypeDensity.member_cell_chart_coset_decomposition
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:27.849781+00:00
-- url     : https://prove2.me/theorems/dfdcb866-eb6f-4772-bcb8-539e3408a868
-- title:
--   Coordinate cosets of level `M ≥ cellDegree` give a finite measurable partition of the coordinate space, and the preimage of a cell in any chart is the union of the cosets whose representatives lie in
-- statement:
--   Coordinate cosets of level `M ≥ cellDegree` give a finite measurable partition of the coordinate space, and the preimage of a cell in any chart is the union of the cosets whose representatives lie in the cell.
-- source:
--   TypeDensity/Measure/MemberCharts.lean#L300-L350

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
import Theorems.Thm_TypeDensity_coordinate_coset_representatives_exist
import Theorems.Thm_TypeDensity_surface_state_vertical_perturbation
import Theorems.Thm_TypeDensity_fixed_tangent_cell_chart_partition
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_concrete_member_charts
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
open scoped Classical

theorem TypeDensity.member_cell_chart_coset_decomposition (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (Mlev : ℕ) (hM : m.toMeasured.cellDegree c ≤ Mlev) :
    ∃ reps : Finset (Fin m.s.degree → m.O),
      (∀ z : Fin m.s.degree → m.O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {m.S.pi}) Mlev z z₀) ∧
      (∀ z₀ : Fin m.s.degree → m.O, MeasurableSet (coordinateCoset m.S.pi Mlev z₀)) ∧
      (reps : Set (Fin m.s.degree → m.O)).PairwiseDisjoint
      (fun z₀ => coordinateCoset m.S.pi Mlev z₀) ∧ ∀ i : m.atlas.ι,
        coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b ⁻¹' m.toMeasured.cell c =
        ⋃ z₀ ∈ reps.filter
        (fun z₀ => coordinateIdeal m.S.pi (m.atlas.chart i).f (m.atlas.chart i).b z₀ ∈
        m.toMeasured.cell c), coordinateCoset m.S.pi Mlev z₀ := by sorry
