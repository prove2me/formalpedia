-- Prove2me | Theorems.Thm_TypeDensity_unramified_generic_fibre_ascent
-- name    : TypeDensity.unramified_generic_fibre_ascent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:37.318031+00:00
-- url     : https://prove2.me/theorems/8d1444e2-fee2-4373-9d57-781ad9320789
-- title:
--   A decomposition `K ⊗[O] B ≃ ∏ᵢ Lᵢ` of the generic fibre ascends along an unramified extension `O → Oδ` (with `π` remaining a uniformizer) to `Kδ ⊗[Oδ] B ≃ ∏ᵢ Lᵢ`, compatibly with the `O`-structures.
-- statement:
--   A decomposition `K ⊗[O] B ≃ ∏ᵢ Lᵢ` of the generic fibre ascends along an unramified extension `O → Oδ` (with `π` remaining a uniformizer) to `Kδ ⊗[Oδ] B ≃ ∏ᵢ Lᵢ`, compatibly with the `O`-structures.
-- source:
--   TypeDensity/Recursion/Events.lean#L851-L920

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
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_unramified_fraction_base_change
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
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.unramified_generic_fibre_ascent (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi)) (B : Type)
    [CommRing B] [Algebra O B] [Algebra Oδ B] [IsScalarTower O Oδ B] (ι : Type)
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra (BaseField O) (L i)]
    [∀ i, FiniteDimensional (BaseField O) (L i)]
    (e : TensorProduct O (BaseField O) B ≃ₐ[BaseField O] (∀ i, L i)) :
    ∃ (_ : ∀ i, Algebra (BaseField Oδ) (L i)) (_ : ∀ i, Algebra Oδ (L i))
        (_ : ∀ i, IsScalarTower Oδ (BaseField Oδ) (L i))
        (_ : ∀ i, FiniteDimensional (BaseField Oδ) (L i))
        (_ : TensorProduct Oδ (BaseField Oδ) B ≃ₐ[BaseField Oδ] (∀ i, L i)),
    ∀ i (c : O),
    algebraMap Oδ (L i) (algebraMap O Oδ c) = algebraMap (BaseField O) (L i)
        (algebraMap O (BaseField O) c) := by sorry
