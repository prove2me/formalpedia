-- Prove2me | Theorems.Thm_TypeDensity_measure_eq_sum_prod_of_preimage
-- name    : TypeDensity.measure_eq_sum_prod_of_preimage
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:50.940228+00:00
-- url     : https://prove2.me/theorems/da4477ff-013a-4ed5-b994-a5d84f4b8ef7
-- title:
--   If `f` is measure preserving from `Measure.pi m` to `ν`, the product of the cells `C j` is conull, and the trace on it of `f ⁻¹' E` is the finite union over `τ ∈ T` of products of the measurable facto
-- statement:
--   If `f` is measure preserving from `Measure.pi m` to `ν`, the product of the cells `C j` is conull, and the trace on it of `f ⁻¹' E` is the finite union over `τ ∈ T` of products of the measurable factor events `C j ∩ Ev j (τ j)` (each family `Ev j` being pairwise disjoint), then the `ν`-mass of `E` is the sum over `T` of the products of the factor masses.
-- source:
--   TypeDensity/Assembly/TypeEvents.lean#L954-L971

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
import Theorems.Thm_TypeDensity_pairwiseDisjoint_pi_events
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
open MeasureTheory

theorem TypeDensity.measure_eq_sum_prod_of_preimage [∀ j, MeasurableSpace (X j)] [MeasurableSpace Y]
    (m : ∀ j, Measure (X j)) [∀ j, SigmaFinite (m j)] {ν : Measure Y} {f : (∀ j, X j) → Y}
    (hf : MeasurePreserving f (Measure.pi m) ν) (C : ∀ j, Set (X j))
    (hC : Measure.pi m (Set.pi Set.univ C)ᶜ = 0) (hm : ∀ j s, m j (C j ∩ s) = m j s)
    (Ev : ∀ j, FactorType → Set (X j)) (hEv : ∀ j τ, MeasurableSet (C j ∩ Ev j τ))
    (huniq : ∀ j τ τ' x, x ∈ Ev j τ → x ∈ Ev j τ' → τ = τ') {E : Set Y} (hE : MeasurableSet E)
    (T : Finset (ι → FactorType))
    (hpre : f ⁻¹' E ∩ Set.pi Set.univ C = ⋃ τ ∈ T, Set.pi Set.univ fun j ↦ C j ∩ Ev j (τ j)) :
    ν E = ∑ τ ∈ T, ∏ j, m j (Ev j (τ j)) := by sorry
