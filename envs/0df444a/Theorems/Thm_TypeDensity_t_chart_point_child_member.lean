-- Prove2me | Theorems.Thm_TypeDensity_t_chart_point_child_member
-- name    : TypeDensity.t_chart_point_child_member
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:55:00.176975+00:00
-- url     : https://prove2.me/theorems/5d75ea44-76cb-4baa-a077-e5f9fa2b5fc7
-- title:
--   A closed point of degree `δ` on the exceptional line of the `t`-chart carries a concrete child member: a concrete surface over a finite free `O`-algebra of rank `δ` (residue field of size `q^δ`) in an
-- statement:
--   A closed point of degree `δ` on the exceptional line of the `t`-chart carries a concrete child member: a concrete surface over a finite free `O`-algebra of rank `δ` (residue field of size `q^δ`) in any prescribed compatible state, with measure-compatible coordinates and an identification of its ring with the completed local ring at the point.
-- source:
--   TypeDensity/Recursion/ChildMembers.lean#L75-L170

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
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_unramified_extension_measure_package
import Theorems.Thm_TypeDensity_unramified_coefficient_measure_pi
import Theorems.Thm_TypeDensity_power_coordinates_transport
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_unramified_coefficient_measure_haar
import Theorems.Thm_TypeDensity_coefficient_measure_pi_one
import Theorems.Thm_TypeDensity_concrete_member_data_exists
import Theorems.Thm_TypeDensity_t_chart_nonrational_point_child_data
import Theorems.Thm_TypeDensity_t_chart_rational_point_child_data
import Theorems.Thm_TypeDensity_unramified_free_module
import Theorems.Thm_TypeDensity_unramified_is_dvr
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
open scoped BigOperators ENNReal TensorProduct
open scoped Classical

theorem TypeDensity.t_chart_point_child_member (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (pi : O) (hpi : Irreducible pi)
    (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)))
    [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
      (surfaceT O pi u a b) ∈ P)
    (δ : ℕ) (hδ : 0 < δ)
    (hdeg : Module.length (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸ P) = (δ : ℕ∞))
    (s' : State)
    (hs' : StateShape (a + b) (if (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) ∈ P then b else 0) s') :
    ∃ mc : ConcreteMember,
    ∃ (_ : Algebra O mc.O) (_ : Module.Finite O mc.O) (_ : Module.Free O mc.O),
    Module.finrank O mc.O = δ ∧
    Nat.card (IsLocalRing.ResidueField mc.O) = Nat.card (IsLocalRing.ResidueField O) ^ δ ∧
    mc.pi = algebraMap O mc.O pi ∧ mc.a = a + b ∧
    mc.b = (if (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) ∈ P then b else 0) ∧
    mc.s = s' ∧
    (∃ pc : mc.O ≃ₗ[O] (Fin δ → O), Continuous pc ∧ Continuous pc.symm ∧ Measurable pc ∧
      Measurable pc.symm ∧
      MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map pc.symm
          (coefficientMeasure O δ))
      ∧ ∀ r : ℕ, coefficientMeasure mc.O r = MeasureTheory.Measure.pi
        (fun _ : Fin r => MeasureTheory.Measure.map pc.symm (coefficientMeasure O δ))) ∧
    ∃ Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P ≃+* mc.R,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) (surfaceT O pi u a b))) = mc.S.t ∧
    ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ∈ P →
      Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) = mc.S.x) ∧
    ∀ c : O,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
      algebraMap O mc.R c := by sorry
