-- Prove2me | Theorems.Thm_TypeDensity_descended_block_type_iff
-- name    : TypeDensity.descended_block_type_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:39:15.545169+00:00
-- url     : https://prove2.me/theorems/a4635da8-7c60-45b8-a835-1afb9944fd43
-- title:
--   For an unramified lift `Φ` and a monic polynomial in the residue cell of `(Φ mod π)^r`, its `O`-type is `scaleType (deg Φ) τ` exactly when the translated block polynomial over `O[X]/(Φ)` has type `τ`.
-- statement:
--   For an unramified lift `Φ` and a monic polynomial in the residue cell of `(Φ mod π)^r`, its `O`-type is `scaleType (deg Φ) τ` exactly when the translated block polynomial over `O[X]/(Φ)` has type `τ`.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L298-L364

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
import Theorems.Thm_TypeDensity_polynomial_type_dvd
import Theorems.Thm_TypeDensity_block_translation_type_iff
import Theorems.Thm_TypeDensity_polynomial_type_map_unramified
import Theorems.Thm_TypeDensity_descended_polynomial_type
import Theorems.Thm_TypeDensity_monicPolyO_map_fraction
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_unramified_fraction_field_lift
import Theorems.Thm_TypeDensity_descend_block_mem_cell
import Theorems.Thm_TypeDensity_unramified_is_dvr
import Theorems.Thm_TypeDensity_block_conjugates_coprime
import Theorems.Thm_TypeDensity_block_descent_bijection
import Theorems.Thm_TypeDensity_polynomial_type_unique
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

theorem TypeDensity.descended_block_type_iff (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)] (r : ℕ)
    (a : Fin (Φ.natDegree * r) → O) (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
    (σ : FactorType) :
    HasPolynomialTypeF O (monicPolynomial O a) σ ↔ ∃ τ : FactorType, HasPolynomialTypeF
      (AdjoinRoot Φ) (monicPolynomial (AdjoinRoot Φ) (pointChart O Φ r a)) τ ∧ σ =
      scaleType Φ.natDegree τ := by sorry
