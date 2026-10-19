-- Prove2me | Theorems.Thm_TypeDensity_child_coordinate_preimage_measure
-- name    : TypeDensity.child_coordinate_preimage_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:36.89472+00:00
-- url     : https://prove2.me/theorems/5bc32a6a-b964-4985-907c-25bbac659794
-- title:
--   The child coordinate map multiplies Haar measure by `q^(a n + k) q⁻¹^n`.
-- statement:
--   The child coordinate map multiplies Haar measure by `q^(a n + k) q⁻¹^n`.
-- source:
--   TypeDensity/Assembly/NullBridges.lean#L170-L223

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
import Theorems.Thm_TypeDensity_strict_normalizer_preimage_measure
import Theorems.Thm_TypeDensity_measurableSet_smul_image
import Theorems.Thm_TypeDensity_child_coordinate_map_scaled
import Theorems.Thm_TypeDensity_strict_normalizer_lattice_image
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

theorem TypeDensity.child_coordinate_preimage_measure (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (a : ℕ) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (H : (Fin n → O) →ₗ[O] R) [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (k : ℕ)
    (ha : k < a) (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E H (Q w) = (pi ^ k) • w)
    (hD : Function.Injective (normalizationLinearPart E H)) [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (hpi : Irreducible pi)
    (hk : Module.length O ((Fin n → O) ⧸ LinearMap.range (normalizationLinearPart E H)) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O => (pi^a) • normalizationLinearPart E H z))
    (hscale : ∀ (m : ℕ) (S : Set (Fin n → O)), MeasurableSet S →
      mu ((fun w : Fin n → O => (pi^m) • w) '' S) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * mu S)
    (T : Set (Fin n → O)) (hT : MeasurableSet T) :
    mu (childCoordinateMap pi a b E H ⁻¹' T) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)^(a*n + k) *
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^n *
          mu (T ∩ Set.range (childCoordinateMap pi a b E H)) := by sorry
