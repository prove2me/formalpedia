-- Prove2me | Theorems.Thm_TypeDensity_member_center_linear_part
-- name    : TypeDensity.member_center_linear_part
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:36.992856+00:00
-- url     : https://prove2.me/theorems/b6459668-fea4-43cf-818a-998be66dca2d
-- title:
--   The linear part of the normalization at a member center is injective, admits a scaled inverse, and has cokernel of length `s · deg - tri(cellDegree)`.
-- statement:
--   The linear part of the normalization at a member center is injective, admits a scaled inverse, and has cokernel of length `s · deg - tri(cellDegree)`.
-- source:
--   TypeDensity/Measure/Haar.lean#L245-L329

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
import Theorems.Thm_TypeDensity_division_equiv_child_coordinates
import Theorems.Thm_TypeDensity_normalization_linear_part_cokernel_length_eq
import Theorems.Thm_TypeDensity_scaled_inverse_from_image_containment
import Theorems.Thm_TypeDensity_strict_quotient_cokernel_length
import Theorems.Thm_TypeDensity_strict_quotient_inclusion_exists
import Theorems.Thm_TypeDensity_strict_quotient_map_exists
import Theorems.Thm_TypeDensity_strict_quotient_map_injective
import Theorems.Thm_TypeDensity_coordinate_module_pi_quotient_length
import Theorems.Thm_TypeDensity_strict_transform_ideal_of_generator
import Theorems.Thm_TypeDensity_linear_image_bound_from_cokernel_length
import Theorems.Thm_TypeDensity_length_scaling_of_residue_card
import Theorems.Thm_TypeDensity_pi_mul_cokernel_length
import Theorems.Thm_TypeDensity_concrete_member_mul_t_injective
import Theorems.Thm_TypeDensity_concrete_member_one_le_degree
import Theorems.Thm_TypeDensity_concrete_member_state_generator_contact_length
import Theorems.Thm_TypeDensity_concrete_member_state_generator_transverse
import Theorems.Thm_TypeDensity_division_quotient_basis_equiv
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

theorem TypeDensity.member_center_linear_part (m : ConcreteMember) (c : m.toMeasured.cellIndex)
    (mc : m.toMeasured.childIdx c → ConcreteMember)
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.O]
    [∀ j, Algebra m.toMeasured.O (mc j).toMeasured.R]
    [∀ j, IsScalarTower m.toMeasured.O (mc j).toMeasured.O (mc j).toMeasured.R]
    (hcard : ∀ j, (mc j).toMeasured.q = m.toMeasured.q ^ m.toMeasured.childDelta c j)
    (alpha : ∀ j, m.toMeasured.R →ₐ[m.toMeasured.O] (mc j).toMeasured.R)
    (e : ∀ j, (mc j).toMeasured.R) (he : ∀ j, e j = (mc j).toMeasured.S.t)
    (hbij : Set.BijOn
      (fun (J : Ideal m.toMeasured.R) (j : m.toMeasured.childIdx c) => strictTransformIdeal
      (alpha j) (e j) (m.toMeasured.cellDegree c) J) (m.toMeasured.cell c)
      (Set.pi Set.univ fun j => (mc j).toMeasured.stateSet))
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
    (s : ℕ) (hs : tri (m.toMeasured.cellDegree c) ≤ s) (cc : (∀ j, (mc j).toMeasured.R))
    (hcc : (algebraMap m.toMeasured.O (∀ j, (mc j).toMeasured.R) m.toMeasured.S.pi) ^ s =
      e ^ m.toMeasured.cellDegree c * cc)
    (f : m.toMeasured.R) (b : Fin m.toMeasured.s.degree → m.toMeasured.R)
    (E₀ : m.toMeasured.R ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × m.toMeasured.R))
    (hE₀ : ∀ w, E₀.symm w = divisionMap f b w) (hf : Ideal.span {f} ∈ m.toMeasured.cell c)
    (g : (∀ j, (mc j).toMeasured.R)) (hg : ∀ j, alpha j f = e j ^ m.toMeasured.cellDegree c * g j)
    (bc : Fin m.toMeasured.s.degree → (∀ j, (mc j).toMeasured.R)) :
    (letI : Module m.toMeasured.O (∀ j, (mc j).toMeasured.R) := Algebra.toModule;
      ∀ (E : (∀ j, (mc j).toMeasured.R) ≃ₗ[m.toMeasured.O]
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) × (∀ j, (mc j).toMeasured.R))),
      (∀ w, E.symm w = divisionMap g bc w) →
      ∃ Q : (Fin m.toMeasured.s.degree → m.toMeasured.O) →ₗ[m.toMeasured.O]
      (Fin m.toMeasured.s.degree → m.toMeasured.O),
      (∀ w, normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b) (Q w) =
      (m.toMeasured.S.pi ^ (s * m.toMeasured.s.degree - tri (m.toMeasured.cellDegree c))) • w) ∧
      Function.Injective (normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b)) ∧
      Module.length m.toMeasured.O
      ((Fin m.toMeasured.s.degree → m.toMeasured.O) ⧸ LinearMap.range
      (normalizationLinearPart E (pulledVariation (AlgHom.pi alpha) cc b))) =
      ((s * m.toMeasured.s.degree - tri (m.toMeasured.cellDegree c) : ℕ) : ℕ∞)) := by sorry
