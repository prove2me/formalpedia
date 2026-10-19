-- Prove2me | Theorems.Thm_TypeDensity_concrete_type_add_of_index_map
-- name    : TypeDensity.concrete_type_add_of_index_map
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:44.367968+00:00
-- url     : https://prove2.me/theorems/f1349fa4-0807-4684-bff0-5349c9d82e21
-- title:
--   Type additivity: if `R/J` embeds with finite-length cokernel into a product of algebras over unramified extensions, then the type of `R/J` is the sum of the residue-scaled types.
-- statement:
--   Type additivity: if `R/J` embeds with finite-length cokernel into a product of algebras over unramified extensions, then the type of `R/J` is the sum of the residue-scaled types.
-- source:
--   TypeDensity/Recursion/Members.lean#L1238-L1265

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
import Theorems.Thm_TypeDensity_algebra_type_of_generic_fibre_equiv
import Theorems.Thm_TypeDensity_algebra_type_pi
import Theorems.Thm_TypeDensity_baseChange_bijective_of_finite_cokernel
import Theorems.Thm_TypeDensity_algebra_type_unramified_descent
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

theorem TypeDensity.concrete_type_add_of_index_map (m : ConcreteMember) (n : ℕ) (mc : Fin n → ConcreteMember)
    [∀ j, Algebra m.O (mc j).O] [∀ j, Module.Finite m.O (mc j).O] [∀ j, Module.Free m.O (mc j).O]
    (δ : Fin n → ℕ) (hrank : ∀ j, Module.finrank m.O (mc j).O = δ j)
    (hpi : ∀ j, Irreducible (algebraMap m.O (mc j).O m.pi)) (J : Ideal m.R) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra m.O (B j)] [∀ j, Algebra (mc j).O (B j)]
    [∀ j, IsScalarTower m.O (mc j).O (B j)] [∀ j, Module.Finite (mc j).O (B j)]
    [∀ j, Module.Free (mc j).O (B j)] (ψ : (m.R ⧸ J) →ₐ[m.O] ∀ j, B j) (hψ : Function.Injective ψ)
    (ℓ : ℕ) (hlen : Module.length m.O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) = (ℓ : ℕ∞))
    (τ : Fin n → FactorType) (hτ : ∀ j, HasAlgebraType (mc j).O (B j) (τ j)) :
    HasAlgebraType m.O (m.R ⧸ J) (∑ j, scaleType (δ j) (τ j)) := by sorry
