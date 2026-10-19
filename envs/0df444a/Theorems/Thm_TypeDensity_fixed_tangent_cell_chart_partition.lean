-- Prove2me | Theorems.Thm_TypeDensity_fixed_tangent_cell_chart_partition
-- name    : TypeDensity.fixed_tangent_cell_chart_partition
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:58.721184+00:00
-- url     : https://prove2.me/theorems/fea9ca2a-5fbf-4e14-aba2-4ae1deb032ae
-- title:
--   Inside a coordinate chart, the fixed tangent cell is the disjoint union of the chart images of the `pi ^ M`-cosets of those representatives that have the prescribed tangent divisor.
-- statement:
--   Inside a coordinate chart, the fixed tangent cell is the disjoint union of the chart images of the `pi ^ M`-cosets of those representatives that have the prescribed tangent divisor.
-- source:
--   TypeDensity/Blowup/H0Comparison.lean#L1081-L1121

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
import Theorems.Thm_TypeDensity_surface_state_vertical_perturbation
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
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
open scoped Classical

theorem TypeDensity.fixed_tangent_cell_chart_partition (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (st : State) (n : ℕ) (b : Fin n → R) (f : R)
    (hf : Ideal.span {f} ∈ surfaceStateSet O R S st)
    (hinj : Function.Injective (coordinateIdeal S.pi f b)) (d M : ℕ) (hM : d ≤ M)
    (D : ExceptionalDivisor (IsLocalRing.ResidueField R)) (reps : Finset (Fin n → O))
    (hreps : ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {S.pi}) M z z₀) :
    fixedTangentCell O R S st d D ∩ Set.range (coordinateIdeal S.pi f b) = ⋃ z₀ ∈ reps.filter
      (fun z₀ => HasTangentDivisor O R S (coordinateIdeal S.pi f b z₀) d D), coordinateIdeal S.pi f
      b '' coordinateCoset S.pi M z₀ ∧ (reps : Set (Fin n → O)).PairwiseDisjoint
      (fun z₀ => coordinateIdeal S.pi f b '' coordinateCoset S.pi M z₀) := by sorry
