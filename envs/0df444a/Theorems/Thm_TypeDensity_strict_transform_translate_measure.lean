-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_translate_measure
-- name    : TypeDensity.strict_transform_translate_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:47.849721+00:00
-- url     : https://prove2.me/theorems/f796c0ac-fd5d-41be-9f75-b4f9c3d7dcb3
-- title:
--   Translating the strict-transform chart computation: the preimage of a set of chart coordinates under the strict transform on the ball of radius `|pi|^(s+a-1)` has measure `q⁻¹^(tri d)` times that of i
-- statement:
--   Translating the strict-transform chart computation: the preimage of a set of chart coordinates under the strict transform on the ball of radius `|pi|^(s+a-1)` has measure `q⁻¹^(tri d)` times that of its image under the coordinate ideal map.
-- source:
--   TypeDensity/Assembly/NullBridges.lean#L275-L329

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
import Theorems.Thm_TypeDensity_strict_chart_one_ball_measure
import Theorems.Thm_TypeDensity_strict_chart_coordinates_commute
import Theorems.Thm_TypeDensity_strict_chart_preimage_set_identity
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

theorem TypeDensity.strict_transform_translate_measure (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R)
    (g e c : C) (b : Fin n → R) (hf : alpha f = e ^ d * g)
    (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)]
    (hΨ : Function.Injective (coordinateIdeal pi g bc)) (k : ℕ) (hk : k < a)
    (Q : (Fin n → O) →ₗ[O] (Fin n → O))
    (hQ : ∀ w, normalizationLinearPart E (pulledVariation alpha c b) (Q w) = (pi^k) • w)
    (hD : Function.Injective (normalizationLinearPart E (pulledVariation alpha c b)))
    [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (hpiO : Irreducible pi)
    (hkl : Module.length O ((Fin n → O) ⧸
      LinearMap.range (normalizationLinearPart E (pulledVariation alpha c b))) = k)
    [IsAdicComplete (Ideal.span {pi}) (Fin n → O)] [TopologicalSpace (Fin n → O)]
    [IsTopologicalAddGroup (Fin n → O)] [CompactSpace (Fin n → O)] [T2Space (Fin n → O)]
    [MeasurableSpace (Fin n → O)] [BorelSpace (Fin n → O)] [MeasurableAdd (Fin n → O)]
    (hgen : ‹MeasurableSpace (Fin n → O)› = adicCylinderSpace (Ideal.span {pi}) (Fin n → O))
    (mu : MeasureTheory.Measure (Fin n → O)) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (hfinite : ∀ j, Finite (AdicQuotient (Ideal.span {pi}) (Fin n → O) j))
    (hcont : Continuous (fun z : Fin n → O =>
      (pi^a) • normalizationLinearPart E (pulledVariation alpha c b) z))
    (hscale : ∀ (m : ℕ) (S : Set (Fin n → O)), MeasurableSet S →
      mu ((fun w : Fin n → O => (pi^m) • w) '' S) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(m*n) * mu S)
    (htri : tri d ≤ s*n) (hkd : k = s*n - tri d) (T : Set (Fin n → O)) (hT : MeasurableSet T) :
    mu (coordinateIdeal pi f b ⁻¹' (strictTransformIdeal alpha e d ⁻¹'
        (coordinateIdeal pi g bc '' T)) ∩ Set.range (coordinateScale pi (s+a-1))) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(tri d) *
        mu (coordinateIdeal pi g bc ⁻¹' (coordinateIdeal pi g bc '' T ∩
          strictTransformIdeal alpha e d ''
            (coordinateIdeal pi f b '' Set.range (coordinateScale pi (s+a-1))))) := by sorry
