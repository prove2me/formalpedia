-- Prove2me | Theorems.Thm_TypeDensity_unramified_extension_measure_package
-- name    : TypeDensity.unramified_extension_measure_package
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:19.097703+00:00
-- url     : https://prove2.me/theorems/00015c97-f8f8-47f1-8806-3b7c85b35e82
-- title:
--   For an unramified lift `Φ`, the ring `O[x] ⧸ (Φ)` is a complete DVR with residue field of cardinality `q^(deg Φ)`, carrying a compact second-countable Borel topology that is adic for its maximal ideal
-- statement:
--   For an unramified lift `Φ`, the ring `O[x] ⧸ (Φ)` is a complete DVR with residue field of cardinality `q^(deg Φ)`, carrying a compact second-countable Borel topology that is adic for its maximal ideal.
-- source:
--   TypeDensity/Measure/Haar.lean#L116-L155

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
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_cylinder_basis
import Theorems.Thm_TypeDensity_adic_congruence_rules
import Theorems.Thm_TypeDensity_power_coordinates_transport
import Theorems.Thm_TypeDensity_base_ideal_coordinates
import Theorems.Thm_TypeDensity_base_ideal_pure
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
open scoped BigOperators ENNReal

theorem TypeDensity.unramified_extension_measure_package (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [TopologicalSpace (AdjoinRoot Φ)] [MeasurableSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hΦ.1)
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hΦ.1) :
    ∃ (_ : IsDomain (AdjoinRoot Φ)) (_ : IsLocalRing (AdjoinRoot Φ)), True ∧
      IsDiscreteValuationRing (AdjoinRoot Φ) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) (AdjoinRoot Φ) ∧
      Finite (IsLocalRing.ResidueField (AdjoinRoot Φ)) ∧
      Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) = residueCard O ^ Φ.natDegree ∧
      IsTopologicalRing (AdjoinRoot Φ) ∧ CompactSpace (AdjoinRoot Φ) ∧ T2Space (AdjoinRoot Φ) ∧
      SecondCountableTopology (AdjoinRoot Φ) ∧ BorelSpace (AdjoinRoot Φ) ∧
      IsAdic (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) := by sorry
