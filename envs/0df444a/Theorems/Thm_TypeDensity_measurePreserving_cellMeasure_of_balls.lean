-- Prove2me | Theorems.Thm_TypeDensity_measurePreserving_cellMeasure_of_balls
-- name    : TypeDensity.measurePreserving_cellMeasure_of_balls
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:35:23.545268+00:00
-- url     : https://prove2.me/theorems/55eaecdb-a6ff-4a0b-ae40-7fc4496b57ca
-- title:
--   A measurable map `f` sending `P`-almost every point into a measurable cell `D` (a single residue class modulo `𝔪`, with `cellMeasure O N D` a probability measure) pushes the probability m
-- statement:
--   A measurable map `f` sending `P`-almost every point into a measurable cell `D` (a single residue class modulo `𝔪`, with `cellMeasure O N D` a probability measure) pushes the probability measure `P` forward to `cellMeasure O N D` as soon as both measures agree on the `𝔪 ^ L`-balls (`L ≥ 1`) centred in `D`.
-- source:
--   TypeDensity/Unramified/HomogeneousCells.lean#L49-L92

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_finite_measures_from_cylinders
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
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.measurePreserving_cellMeasure_of_balls (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) {α : Type} [MeasurableSpace α]
    (P : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure P] (N : ℕ)
    (D : Set (Fin N → O)) (hDm : MeasurableSet D)
    [MeasureTheory.IsProbabilityMeasure (cellMeasure O N D)]
    (hDball : ∀ z ∈ D, D = {y | ∀ j, y j - z j ∈ IsLocalRing.maximalIdeal O})
    (f : α → Fin N → O) (hf : Measurable f) (S : Set α) (hS : P Sᶜ = 0)
    (hSD : Set.MapsTo f S D)
    (hball : ∀ L, 1 ≤ L → ∀ x ∈ D,
      P (f ⁻¹' {y | ∀ j, y j - x j ∈ IsLocalRing.maximalIdeal O ^ L}) =
        cellMeasure O N D {y | ∀ j, y j - x j ∈ IsLocalRing.maximalIdeal O ^ L}) :
    MeasureTheory.MeasurePreserving f P (cellMeasure O N D) := by sorry
