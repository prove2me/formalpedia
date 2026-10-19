-- Prove2me | Theorems.Thm_TypeDensity_state_measure_atlas_independent
-- name    : TypeDensity.state_measure_atlas_independent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:47.534802+00:00
-- url     : https://prove2.me/theorems/1f8eff50-639f-4cff-90fd-1b94257ca9b5
-- title:
--   The state measure does not depend on the ideal atlas used to define it.
-- statement:
--   The state measure does not depend on the ideal atlas used to define it.
-- source:
--   TypeDensity/Measure/Atlas.lean#L277-L313

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
import Theorems.Thm_TypeDensity_division_data_same_cell_recenter
import Theorems.Thm_TypeDensity_ideal_chart_pushforward_independent
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.state_measure_atlas_independent (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (hpi : Irreducible pi) (n : ℕ) (X : Set (Ideal R))
    (A B : IdealAtlas O R pi n X)
    (hB : ∀ j, Measurable (coordinateIdeal pi (B.chart j).f (B.chart j).b)) (e : A.ι ≃ B.ι)
    (hcell : ∀ i, residueIdealCell (algebraMap O R pi) (A.chart i).f =
      residueIdealCell (algebraMap O R pi) (B.chart (e i)).f)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] [IsDomain R] [IsLocalRing R]
    (hp0 : algebraMap O R pi ≠ 0) (hpm : algebraMap O R pi ∈ IsLocalRing.maximalIdeal R) :
    stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) A =
      stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) B := by sorry
