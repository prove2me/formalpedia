-- Prove2me | Theorems.Thm_TypeDensity_cell_member_index_map
-- name    : TypeDensity.cell_member_index_map
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:02:19.07699+00:00
-- url     : https://prove2.me/theorems/f4e5f1cb-e777-4bb8-9742-23b8c6b4af3f
-- title:
--   **The index map of a cell.** For a cell ideal `J` of a concrete member and child quotients `B j ≅ R_j ⧸ Φ J j`, there is an injective `O`-algebra map `R ⧸ J → ∏ B j` with cokernel of length `d(d-1)/2`
-- statement:
--   **The index map of a cell.** For a cell ideal `J` of a concrete member and child quotients `B j ≅ R_j ⧸ Φ J j`, there is an injective `O`-algebra map `R ⧸ J → ∏ B j` with cokernel of length `d(d-1)/2` (`d` the cell degree), compatible with the child maps `α j`.
-- source:
--   TypeDensity/Recursion/RootCellLaw.lean#L722-L811

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
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Definitions.Def_TypeDensity_Recursion_RootCellLaw
import Theorems.Thm_TypeDensity_parent_ideal_unique_of_level_lattice
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
import Theorems.Thm_TypeDensity_two_chart_common_multiplicity_eq
import Theorems.Thm_TypeDensity_fixed_tangent_cell_curve_datum
import Theorems.Thm_TypeDensity_chart_point_eq_directionPoint
import Theorems.Thm_TypeDensity_concrete_two_chart_glued_generators_exist
import Theorems.Thm_TypeDensity_has_tangent_divisor_multiplicity
import Theorems.Thm_TypeDensity_actual_blowup_restriction_exists
import Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_multiplicity
import Theorems.Thm_TypeDensity_concrete_strict_transform_multiplicity
import Theorems.Thm_TypeDensity_strict_transforms_give_level_lattice_membership
import Theorems.Thm_TypeDensity_two_chart_right_points_maximal
import Theorems.Thm_TypeDensity_two_chart_left_generators_regular_on_overlap
import Theorems.Thm_TypeDensity_cell_datum_point_equiv
import Theorems.Thm_TypeDensity_cell_child_Phi_eq_map
import Theorems.Thm_TypeDensity_concrete_index_map_reindexed
import Theorems.Thm_TypeDensity_two_chart_datum_concrete_instances
import Theorems.Thm_TypeDensity_concrete_surface_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_xt
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
open scoped BigOperators ENNReal

theorem TypeDensity.cell_member_index_map (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (hJ : J ∈ m.toMeasured.cell c) (B : m.toMeasured.childIdx c → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] (eB : ∀ j, B j ≃+* (D.mc j).R ⧸ D.Φ J j)
    (hB : ∀ (j : m.toMeasured.childIdx c) (r : m.O), eB j (algebraMap m.O (B j) r) =
    Ideal.Quotient.mk (D.Φ J j) (algebraMap m.O (D.mc j).R r)) :
    ∃ ψ : (m.R ⧸ J) →ₐ[m.O] ∀ j, B j, Function.Injective ψ ∧ Module.length m.O
        ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = (chooseTwo (m.toMeasured.cellDegree c) : ℕ∞)
        ∧ ∀ (r : m.R) (j : m.toMeasured.childIdx c), eB j (ψ (Ideal.Quotient.mk J r) j) =
        Ideal.Quotient.mk (D.Φ J j) (D.alpha j r) := by sorry
