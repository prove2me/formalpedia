-- Prove2me | Theorems.Thm_TypeDensity_orig_projectiveDensity_eq
-- name    : TypeDensity.orig_projectiveDensity_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:28.132663+00:00
-- url     : https://prove2.me/theorems/39fc0365-f2e3-4381-8dde-3d9290a41d85
-- title:
--   The original projective density equals the route-F one: the two numerator events differ only inside `{a_n = 0} ∪ {disc = 0}`, which is Haar-null.
-- statement:
--   The original projective density equals the route-F one: the two numerator events differ only inside `{a_n = 0} ∪ {disc = 0}`, which is Haar-null.
-- source:
--   TypeDensity/Assembly/NullBridges.lean#L472-L486

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
import Theorems.Thm_TypeDensity_hasPolynomialTypeF_iff_of_separable
import Theorems.Thm_TypeDensity_monic_polynomial_degree
import Theorems.Thm_TypeDensity_coordinate_hyperplane_null
import Theorems.Thm_TypeDensity_separable_of_resultant
import Theorems.Thm_TypeDensity_resultant_ne_zero_of_separable
import Theorems.Thm_TypeDensity_affine_resultant_eq
import Theorems.Thm_TypeDensity_exists_separable_monic
import Theorems.Thm_TypeDensity_coefficientMeasure_zero_null
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
open MeasureTheory Polynomial
open scoped BigOperators ENNReal
variable (O : Type) [CommRing O] [IsDomain O]
variable [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]

theorem TypeDensity.orig_projectiveDensity_eq (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (σ : FactorType) :
    TypeDensity.projectiveDensity O n σ = projectiveDensityF O n σ := by sorry
