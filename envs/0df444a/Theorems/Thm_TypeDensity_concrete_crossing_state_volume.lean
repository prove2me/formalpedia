-- Prove2me | Theorems.Thm_TypeDensity_concrete_crossing_state_volume
-- name    : TypeDensity.concrete_crossing_state_volume
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:46:17.962749+00:00
-- url     : https://prove2.me/theorems/a5b8ed0a-c380-4fdf-964e-3303558264cc
-- title:
--   The crossing state `(a, b, c, h)` of the concrete surface has measure `(q - 1) q^(-(c + h))`, where `q` is the size of the residue field.
-- statement:
--   The crossing state `(a, b, c, h)` of the concrete surface has measure `(q - 1) q^(-(c + h))`, where `q` is the size of the residue field.
-- source:
--   TypeDensity/Surfaces/ConcreteStrictTransforms.lean#L71-L110

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
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_IdealChart_isDivisionChart
import Theorems.Thm_TypeDensity_crossing_state_volume
import Theorems.Thm_TypeDensity_division_coordinate_module_isAdicComplete
import Theorems.Thm_TypeDensity_concrete_crossing_state_atlas_exists
import Theorems.Thm_TypeDensity_coordinate_ideal_measurable_chart_sigma
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
open scoped ENNReal

theorem TypeDensity.concrete_crossing_state_volume (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = surfaceT O pi u a b) (hSx : S.x = surfaceX O pi u a b) (hSa : S.a = a)
    (hSb : S.b = b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b)
      (residueSeries O s)) (c h : ℕ) (hc : 0 < c) (hh : 0 < h) [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    (letI : MeasurableSpace (Ideal (ConcreteSurface O pi u a b)) := idealChartSigma O
        (ConcreteSurface O pi u a b) pi; ∃ A : IdealAtlas O (ConcreteSurface O pi u a b) pi
        (a*c+b*h) (surfaceStateSet O (ConcreteSurface O pi u a b) S (State.crossing a b c h)),
        stateMeasure O (ConcreteSurface O pi u a b) pi (a*c+b*h)
        (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
        ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞) - 1) *
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(c+h)) := by sorry
