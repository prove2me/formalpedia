-- Prove2me | Theorems.Thm_TypeDensity_projective_cell_affine_type_event
-- name    : TypeDensity.projective_cell_affine_type_event
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T17:17:03.471481+00:00
-- url     : https://prove2.me/theorems/197fa6d0-4ec8-4d2e-9f10-87c28e810cd8
-- title:
--   Assuming the root cell law, the projective cell of a divisor with array `m` has law `arrayLaw m` for affine type events.
-- statement:
--   Assuming the root cell law, the projective cell of a divisor with array `m` has law `arrayLaw m` for affine type events.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L1215-L1252

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
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Theorems.Thm_TypeDensity_divisor_form_cell_law
import Theorems.Thm_TypeDensity_affine_type_event_unit_scaling
import Theorems.Thm_TypeDensity_divisor_vector_properties
import Theorems.Thm_TypeDensity_cellMeasure_cell_inter
import Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
import Theorems.Thm_TypeDensity_projective_cell_mass
import Theorems.Thm_TypeDensity_projective_cell_normalization_pushforward
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

theorem TypeDensity.projective_cell_affine_type_event (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField O))
    (hD : exceptionalDegree (IsLocalRing.ResidueField O) D = n) (m : Pattern n)
    (hm : HasArray (IsLocalRing.ResidueField O) n D m) (σ : FactorType) :
    MeasurableSet (projectiveCell O n (divisorVector (IsLocalRing.ResidueField O) n D) ∩
      affineTypeEvent O n σ) ∧ cellMeasure O (n+1) (projectiveCell O n
      (divisorVector (IsLocalRing.ResidueField O) n D)) (affineTypeEvent O n σ) = densityValue
      (lawCoeff (arrayLaw m) σ) (Nat.card (IsLocalRing.ResidueField O)) := by sorry
