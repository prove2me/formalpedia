-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_data_exists
-- name    : TypeDensity.concrete_member_data_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:44:50.803214+00:00
-- url     : https://prove2.me/theorems/c0e6f20c-daf8-485e-a5bf-e3fcb0d72965
-- title:
--   Every admissible shape is realized: the concrete surface carries surface data with the concrete parameters and an ideal atlas of the state set.
-- statement:
--   Every admissible shape is realized: the concrete surface carries surface data with the concrete parameters and an ideal atlas of the state set.
-- source:
--   TypeDensity/Recursion/Members.lean#L839-L870

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
import Theorems.Thm_TypeDensity_concrete_crossing_state_atlas_exists
import Theorems.Thm_TypeDensity_concrete_single_state_atlas_exists
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv
import Theorems.Thm_TypeDensity_concrete_surface_data_exists_unconditional
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

theorem TypeDensity.concrete_member_data_exists (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a) (s : State)
    (hs : StateShape a b s) :
    ∃ (_ : IsDomain (ConcreteSurface O pi u a b)) (_ : IsRegularLocalRing
      (ConcreteSurface O pi u a b)) (S : SurfaceData O (ConcreteSurface O pi u a b)), S.pi = pi ∧
      S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b ∧ S.a = a ∧ S.b = b ∧ Nonempty
      (IdealAtlas O (ConcreteSurface O pi u a b) S.pi s.degree
      (surfaceStateSet O (ConcreteSurface O pi u a b) S s)) := by sorry
