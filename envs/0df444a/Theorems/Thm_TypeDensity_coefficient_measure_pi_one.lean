-- Prove2me | Theorems.Thm_TypeDensity_coefficient_measure_pi_one
-- name    : TypeDensity.coefficient_measure_pi_one
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:17.734757+00:00
-- url     : https://prove2.me/theorems/63f56efc-bb73-4a40-a233-e050df29455b
-- title:
--   The coefficient Haar measure on `O^r` is the product of the coefficient measure on `O`, transported along `O^1 ≃ O`, which is a homeomorphic measurable equivalence.
-- statement:
--   The coefficient Haar measure on `O^r` is the product of the coefficient measure on `O`, transported along `O^1 ≃ O`, which is a homeomorphic measurable equivalence.
-- source:
--   TypeDensity/Recursion/Members.lean#L750-L780

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
import Theorems.Thm_TypeDensity_coefficient_space_strict_instances
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

theorem TypeDensity.coefficient_measure_pi_one (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] [SecondCountableTopology O]
    [MeasurableSpace O] [BorelSpace O] (htop : IsAdic (maximalIdeal O)) (pi : O)
    (hpi : Irreducible pi) (r : ℕ) [SigmaFinite ((coefficientMeasure O 1).map
    (LinearEquiv.funUnique (Fin 1) O O))] :
    coefficientMeasure O r = Measure.pi (fun _ : Fin r => (coefficientMeasure O 1).map
      (LinearEquiv.funUnique (Fin 1) O O)) ∧ IsProbabilityMeasure
      ((coefficientMeasure O 1).map (LinearEquiv.funUnique (Fin 1) O O)) ∧ Continuous
      (LinearEquiv.funUnique (Fin 1) O O) ∧ Continuous (LinearEquiv.funUnique (Fin 1) O O).symm ∧
      Measurable (LinearEquiv.funUnique (Fin 1) O O) ∧ Measurable
      (LinearEquiv.funUnique (Fin 1) O O).symm := by sorry
