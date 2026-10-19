-- Prove2me | Theorems.Thm_TypeDensity_chart_cell_law_generic
-- name    : TypeDensity.chart_cell_law_generic
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:34:12.924287+00:00
-- url     : https://prove2.me/theorems/44ec5972-d79d-4e98-a5e8-357369ba8720
-- title:
--   Transfer of a cell law through a single coordinate chart: if a chart covers the set `X` and the type event in `X` agrees up to a null set with a set of measure given by the law, then the coefficient m
-- statement:
--   Transfer of a cell law through a single coordinate chart: if a chart covers the set `X` and the type event in `X` agrees up to a null set with a set of measure given by the law, then the coefficient measure of the polynomial type event equals the law density, and `μ X = q⁻ʳ`.
-- source:
--   TypeDensity/Recursion/Members.lean#L690-L748

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
import Theorems.Thm_TypeDensity_coefficient_measure_probability
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

theorem TypeDensity.chart_cell_law_generic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (R : Type) [CommRing R] [Algebra O R] [MeasurableSpace (Ideal R)] (r : ℕ) (f : R)
    (b : Fin r → R) (hmeas : Measurable (coordinateIdeal pi f b))
    (X : Set (Ideal R)) (hcell : ∀ z : Fin r → O, coordinateIdeal pi f b z ∈ X)
    (μ : Measure (Ideal R)) (hμ : μ = (((Nat.card (ResidueField O)) : ℝ≥0∞)⁻¹ ^ r) •
    (coefficientMeasure O r).map (coordinateIdeal pi f b)) (htype : ∀ (z : Fin r → O)
    (σ : FactorType), HasAlgebraType O (R ⧸ coordinateIdeal pi f b z) σ ↔ HasPolynomialTypeF O
    (monicPolynomial O (pi • z)) σ) (σ : FactorType) (F N : Set (Ideal R)) (hFm : MeasurableSet F)
    (hFE : F ⊆ {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ}) (hEF :
    {J | J ∈ X ∧ HasAlgebraType O (R ⧸ J) σ} ⊆ F ∪ N) (hN : μ N = 0)
    (hF : μ F = densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (Nat.card (ResidueField O))
    * μ X) :
    coefficientMeasure O r {z : Fin r → O | HasPolynomialTypeF O (monicPolynomial O (pi • z)) σ} =
      densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (Nat.card (ResidueField O)) ∧ μ X =
      ((Nat.card (ResidueField O)) : ℝ≥0∞)⁻¹ ^ r := by sorry
