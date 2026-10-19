-- Prove2me | Theorems.Thm_TypeDensity_infinity_point_child_member
-- name    : TypeDensity.infinity_point_child_member
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:54:13.16099+00:00
-- url     : https://prove2.me/theorems/cbdb8354-d6a7-463d-99d2-ca64b8dfff88
-- title:
--   The completed local ring at the point at infinity of a concrete surface is a concrete member of shape `(a + b, a)` over the same coefficient ring, with the expected boundary parameters.
-- statement:
--   The completed local ring at the point at infinity of a concrete surface is a concrete member of shape `(a + b, a)` over the same coefficient ring, with the expected boundary parameters.
-- source:
--   TypeDensity/Recursion/Termination.lean#L855-L899

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
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_coefficient_measure_pi_one
import Theorems.Thm_TypeDensity_concrete_member_data_exists
import Theorems.Thm_TypeDensity_x_chart_infinity_completion_equiv
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.infinity_point_child_member (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime] (s' : State) (hs' : StateShape (a + b) a s') :
    ∃ mc : ConcreteMember, ∃ (_ : Algebra O mc.O) (_ : Module.Finite O mc.O)
      (_ : Module.Free O mc.O), Module.finrank O mc.O = 1 ∧ Nat.card (ResidueField mc.O) = Nat.card
      (ResidueField O) ^ 1 ∧ mc.pi = algebraMap O mc.O pi ∧ mc.a = a + b ∧ mc.b = a ∧ mc.s = s' ∧
      (∃ pc : mc.O ≃ₗ[O] (Fin 1 → O), Continuous pc ∧ Continuous pc.symm ∧ Measurable pc ∧
      Measurable pc.symm ∧ IsProbabilityMeasure (Measure.map pc.symm (coefficientMeasure O 1)) ∧ ∀ r
      : ℕ, coefficientMeasure mc.O r = Measure.pi (fun _ : Fin r => Measure.map pc.symm
      (coefficientMeasure O 1))) ∧ ∃ Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b)
      (surfaceX O pi u a b) (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+* mc.R, Eq
      ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (surfaceX O pi u a b))) = mc.S.t ∧ Eq
      ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b)) (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))) (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b))) = mc.S.x ∧ ∀ c : O, Eq ((completedPointMap
      (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
      (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
      ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
      (algebraMap O (ConcreteSurface O pi u a b) c))) = algebraMap O mc.R c := by sorry
