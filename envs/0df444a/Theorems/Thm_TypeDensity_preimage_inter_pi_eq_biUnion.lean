-- Prove2me | Theorems.Thm_TypeDensity_preimage_inter_pi_eq_biUnion
-- name    : TypeDensity.preimage_inter_pi_eq_biUnion
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:11.090082+00:00
-- url     : https://prove2.me/theorems/1255d032-d5cf-4a84-9c24-dd5fbae0feb0
-- title:
--   If `f` maps the product of the cells `C j` into `E₀`, and a point `a` of that product has `f a ∈ P` exactly when `a j ∈ Ev j (τ j)` for some `τ` with `σ = ∑ j, τ j`, then the trace of `f ⁻¹' (E₀ ∩ P)`
-- statement:
--   If `f` maps the product of the cells `C j` into `E₀`, and a point `a` of that product has `f a ∈ P` exactly when `a j ∈ Ev j (τ j)` for some `τ` with `σ = ∑ j, τ j`, then the trace of `f ⁻¹' (E₀ ∩ P)` on the product is a finite union of products of events.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L913-L932

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
variable {ι Y : Type} [Fintype ι] {X : ι → Type}

theorem TypeDensity.preimage_inter_pi_eq_biUnion (f : (∀ j, X j) → Y) (C : ∀ j, Set (X j))
    (E₀ P : Set Y) (hf : Set.MapsTo f (Set.pi Set.univ C) E₀) (Ev : ∀ j, FactorType → Set (X j))
    (W : ι → Finset FactorType) (hW : ∀ j τ, (C j ∩ Ev j τ).Nonempty → τ ∈ W j)
    (σ : FactorType) (hP : ∀ a ∈ Set.pi Set.univ C,
      f a ∈ P ↔ ∃ τ : ι → FactorType, (∀ j, a j ∈ Ev j (τ j)) ∧ σ = ∑ j, τ j)
    (T : Finset (ι → FactorType)) (hT : ∀ τ, τ ∈ T ↔ (∀ j, τ j ∈ W j) ∧ σ = ∑ j, τ j) :
    f ⁻¹' (E₀ ∩ P) ∩ Set.pi Set.univ C = ⋃ τ ∈ T, Set.pi Set.univ fun j ↦ C j ∩ Ev j (τ j) := by sorry
