-- Prove2me | Theorems.Thm_TypeDensity_concrete_residue_ideal_chart_exists
-- name    : TypeDensity.concrete_residue_ideal_chart_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:36.740619+00:00
-- url     : https://prove2.me/theorems/2bc4060a-36d8-4c0b-abca-bda9d7db4559
-- title:
--   Every non-unit, non-zero-divisor `f̄` of the special fiber lifts to an ideal chart of the concrete surface whose reduction generates the same ideal as `f̄`.
-- statement:
--   Every non-unit, non-zero-divisor `f̄` of the special fiber lifts to an ideal chart of the concrete surface whose reduction generates the same ideal as `f̄`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L239-L286

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
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_length_transport
import Theorems.Thm_TypeDensity_division_linear_equivalence
import Theorems.Thm_TypeDensity_concrete_surface_residue_regular_of_special_fiber
import Theorems.Thm_TypeDensity_concrete_surface_isDomain
import Theorems.Thm_TypeDensity_concrete_surface_curve_free_of_length
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_residue_ideal_chart_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (fbar : SpecialFiber (IsLocalRing.ResidueField O) a b) (hunit : ¬ IsUnit fbar)
    (hreg : Function.Injective (fun w : SpecialFiber (IsLocalRing.ResidueField O) a b => fbar * w))
    (N : ℕ) (hN : Module.length (SpecialFiber (IsLocalRing.ResidueField O) a b)
      (SpecialFiber (IsLocalRing.ResidueField O) a b ⧸ Ideal.span {fbar}) = N) :
    ∃ ch : IdealChart O (ConcreteSurface O pi u a b) pi N,
      Ideal.span
      {e ((Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})) ch.f)} =
      Ideal.span {fbar} := by sorry
