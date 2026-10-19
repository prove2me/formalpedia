-- Prove2me | Theorems.Thm_TypeDensity_fixed_tangent_cell_chart_measurable
-- name    : TypeDensity.fixed_tangent_cell_chart_measurable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:26.651397+00:00
-- url     : https://prove2.me/theorems/affcc421-2d0c-4e4a-beac-754f81513a9b
-- title:
--   The part of a fixed tangent cell inside a coordinate chart is measurable for the chart σ-algebra.
-- statement:
--   The part of a fixed tangent cell inside a coordinate chart is measurable for the chart σ-algebra.
-- source:
--   TypeDensity/Blowup/H0Comparison.lean#L1123-L1139

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
import Theorems.Thm_TypeDensity_fixed_tangent_cell_chart_partition
import Theorems.Thm_TypeDensity_chart_image_measurable_chart_sigma
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
open scoped BigOperators ENNReal

theorem TypeDensity.fixed_tangent_cell_chart_measurable (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    [MeasurableSpace O] (S : SurfaceData O R) (st : State) (n : ℕ) (b : Fin n → R) (f : R)
    (hf : Ideal.span {f} ∈ surfaceStateSet O R S st)
    (hinj : Function.Injective (coordinateIdeal S.pi f b)) (hchart : IsDivisionChart O R S.pi f b)
    (d M : ℕ) (hM : d ≤ M) (D : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (reps : Finset (Fin n → O))
    (hreps : ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {S.pi}) M z z₀)
    (hcoset : ∀ z₀ : Fin n → O, MeasurableSet (coordinateCoset S.pi M z₀)) :
    @MeasurableSet (Ideal R) (idealChartSigma O R S.pi)
      (fixedTangentCell O R S st d D ∩ Set.range (coordinateIdeal S.pi f b)) := by sorry
