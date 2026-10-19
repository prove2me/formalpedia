-- Prove2me | Theorems.Thm_TypeDensity_etale_invariant_children
-- name    : TypeDensity.etale_invariant_children
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:48.557968+00:00
-- url     : https://prove2.me/theorems/7eee380f-bbd3-47eb-a41e-eb8c1a0845ab
-- title:
--   The order defects of the children `Bⱼ`, measured over their own DVRs `Oⱼ` (in which `π` stays a uniformizer), are at most the order defect of `A`, and strictly smaller when `ℓ ≥ 1`.
-- statement:
--   The order defects of the children `Bⱼ`, measured over their own DVRs `Oⱼ` (in which `π` stays a uniformizer), are at most the order defect of `A`, and strictly smaller when `ℓ ≥ 1`.
-- source:
--   TypeDensity/Recursion/OrderDefect.lean#L230-L254

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
import Theorems.Thm_TypeDensity_order_defect_child_le
import Theorems.Thm_TypeDensity_full_rank_free_submodule_finite_length
import Theorems.Thm_TypeDensity_generic_closure_free_of_type
import Theorems.Thm_TypeDensity_order_defect_le_of_tower
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

theorem TypeDensity.etale_invariant_children (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n : ℕ) (Oj : Fin n → Type) [∀ j, CommRing (Oj j)]
    [∀ j, IsDomain (Oj j)] [∀ j, IsDiscreteValuationRing (Oj j)] [∀ j, Algebra O (Oj j)]
    [∀ j, Module.Finite O (Oj j)] [∀ j, Module.Free O (Oj j)] (δ : Fin n → ℕ)
    (hrank : ∀ j, Module.finrank O (Oj j) = δ j) (pi : O) (hpi : Irreducible pi)
    (hpiδ : ∀ j, Irreducible (algebraMap O (Oj j) pi)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Free O A] (B : Fin n → Type) [∀ j, CommRing (B j)]
    [∀ j, Algebra O (B j)] [∀ j, Module.Finite O (B j)] [∀ j, Module.Free O (B j)]
    [∀ j, Algebra (Oj j) (B j)] [∀ j, IsScalarTower O (Oj j) (B j)] (ψ : A →ₐ[O] ∀ j, B j)
    (hinj : Function.Injective ψ) (ℓ : ℕ)
    (hℓ : Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = ℓ) (σ : FactorType)
    (hσ : HasAlgebraType O A σ) :
    ∀ j, (orderDefect (Oj j) (B j)).toNat ≤ (orderDefect O A).toNat ∧
    (1 ≤ ℓ → (orderDefect (Oj j) (B j)).toNat < (orderDefect O A).toNat) := by sorry
