-- Prove2me | Theorems.Thm_TypeDensity_member_cell_chart_box
-- name    : TypeDensity.member_cell_chart_box
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:01:41.258535+00:00
-- url     : https://prove2.me/theorems/e2c9e4d2-eb1b-4a32-9d24-3ebbc451e44c
-- title:
--   In the chart `i` of a cell, given coset representatives `reps` of level `s + a - 1`, the chart preimage of the box `{J ∈ cell : cellStrict J ∈ Π G_j}` is measurable, and its measure is `q^(-tri(cellDe
-- statement:
--   In the chart `i` of a cell, given coset representatives `reps` of level `s + a - 1`, the chart preimage of the box `{J ∈ cell : cellStrict J ∈ Π G_j}` is measurable, and its measure is `q^(-tri(cellDegree)) q^deg` times the sum, over the representatives landing in the cell, of the child measures of the images of the corresponding cosets.
-- source:
--   TypeDensity/Measure/MemberBoxes.lean#L415-L487

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
import Theorems.Thm_TypeDensity_measurableSet_smul_image
import Theorems.Thm_TypeDensity_strict_transform_translate_measure
import Theorems.Thm_TypeDensity_coefficient_space_strict_instances
import Theorems.Thm_TypeDensity_child_coordinate_map_scaled
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_coordinate_scale_measure
import Theorems.Thm_TypeDensity_strict_normalizer_lattice_image
import Theorems.Thm_TypeDensity_strict_chart_coordinates_commute
import Theorems.Thm_TypeDensity_strict_chart_preimage_set_identity
import Theorems.Thm_TypeDensity_pi_strict_transform_map_eval
import Theorems.Thm_TypeDensity_product_chart_projection
import Theorems.Thm_TypeDensity_strict_transform_ideal_of_generator
import Theorems.Thm_TypeDensity_member_center_linear_part
import Theorems.Thm_TypeDensity_isAdicComplete_pi
import Theorems.Thm_TypeDensity_pi_algebraMap_mem_jacobson_bot
import Theorems.Thm_TypeDensity_product_coordinates_exist
import Theorems.Thm_TypeDensity_product_division_equiv
import Theorems.Thm_TypeDensity_member_chart_translate
import Theorems.Thm_TypeDensity_member_coefficient_measure_map_product_coordinates
import Theorems.Thm_TypeDensity_member_product_chart_pushforward
import Theorems.Thm_TypeDensity_concrete_member_division_module_isAdicComplete
import Theorems.Thm_TypeDensity_concrete_member_mul_t_injective
import Theorems.Thm_TypeDensity_concrete_member_one_le_degree
import Theorems.Thm_TypeDensity_concrete_member_state_generator_regular
import Theorems.Thm_TypeDensity_concrete_member_division_chart_measure
import Theorems.Thm_TypeDensity_concrete_member_state_generator_division
import Theorems.Thm_TypeDensity_scaled_strict_map_measurable
import Theorems.Thm_TypeDensity_division_data_vertical_perturbation
import Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_span_pi_base
import Theorems.Thm_TypeDensity_coordinate_ideal_measurable_chart_sigma
import Theorems.Thm_TypeDensity_dvr_isAdicComplete_span_uniformizer
import Theorems.Thm_TypeDensity_isAdicComplete_prod
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
open scoped Classical
include pc hpc hpc' hdeg hstrict

theorem TypeDensity.member_cell_chart_box (s : ℕ) (hs : tri (m.toMeasured.cellDegree c) ≤ s) (cc : (∀ j, (mc j).toMeasured.R))
    (hcc : (algebraMap (m.toMeasured.O) (∀ j, (mc j).toMeasured.R) (m.toMeasured.S.pi)) ^ s = e ^ (m.toMeasured.cellDegree c) * cc) (a : ℕ) (ha : a = s * (m.toMeasured.s.degree) - tri (m.toMeasured.cellDegree c) + 1)
    (reps : Finset (Fin (m.toMeasured.s.degree) → (m.toMeasured.O))) (hrdisj : (reps : Set (Fin (m.toMeasured.s.degree) → (m.toMeasured.O))).PairwiseDisjoint (coordinateCoset (m.toMeasured.S.pi) (s + a - 1)))
    (i : m.atlas.ι)
    (hdec : memberChart m i ⁻¹' m.toMeasured.cell c =
      ⋃ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
        coordinateCoset (m.toMeasured.S.pi) (s + a - 1) z₀)
    (G : ∀ j, Set (Ideal (mc j).toMeasured.R)) (hG : ∀ j, MeasurableSet (G j)) :
    MeasurableSet (memberChart m i ⁻¹' (m.toMeasured.cell c ∩ (fun (J : Ideal (m.toMeasured.R)) (j : (m.toMeasured.childIdx c)) => strictTransformIdeal (alpha j) (e j) (m.toMeasured.cellDegree c) J) ⁻¹' Set.pi Set.univ G)) ∧
    coefficientMeasure (m.toMeasured.O) (m.toMeasured.s.degree)
        (memberChart m i ⁻¹' (m.toMeasured.cell c ∩ (fun (J : Ideal (m.toMeasured.R)) (j : (m.toMeasured.childIdx c)) => strictTransformIdeal (alpha j) (e j) (m.toMeasured.cellDegree c) J) ⁻¹' Set.pi Set.univ G)) =
      ((m.toMeasured.q : ℝ≥0∞))⁻¹ ^ tri (m.toMeasured.cellDegree c) * ((m.toMeasured.q : ℝ≥0∞)) ^ (m.toMeasured.s.degree) *
        ∑ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
        Measure.pi (fun j => (mc j).toMeasured.μ) (Set.pi Set.univ G ∩
          (fun (J : Ideal (m.toMeasured.R)) (j : (m.toMeasured.childIdx c)) => strictTransformIdeal (alpha j) (e j) (m.toMeasured.cellDegree c) J) '' (memberChart m i '' coordinateCoset (m.toMeasured.S.pi) (s + a - 1) z₀)) ∧
    ∀ z₀ ∈ reps.filter (fun z₀ => memberChart m i z₀ ∈ m.toMeasured.cell c),
      MeasurableSet ((fun (J : Ideal (m.toMeasured.R)) (j : (m.toMeasured.childIdx c)) => strictTransformIdeal (alpha j) (e j) (m.toMeasured.cellDegree c) J) '' (memberChart m i '' coordinateCoset (m.toMeasured.S.pi) (s + a - 1) z₀)) := by sorry
