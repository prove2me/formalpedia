-- Prove2me | Theorems.Thm_TypeDensity_child_order_equiv_linear
-- name    : TypeDensity.child_order_equiv_linear
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:26:14.51247+00:00
-- url     : https://prove2.me/theorems/aec92aec-f29d-4796-b6f2-75df74798ba8
-- title:
--   The curve order limit is `O`-linearly isomorphic to the child order, compatibly with the maps from surface functions.
-- statement:
--   The curve order limit is `O`-linearly isomorphic to the child order, compatibly with the maps from surface functions.
-- source:
--   TypeDensity/Blowup/TwoChartCurveData.lean#L589-L672

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
import Theorems.Thm_TypeDensity_curve_quotient_complete_equiv_threads
import Theorems.Thm_TypeDensity_curve_limit_equiv_product_threads
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

theorem TypeDensity.child_order_equiv_linear (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    [∀ p : AllPoints D, IsLocalRing (localRing D p)] [∀ p : AllPoints D,
    IsNoetherianRing (localRing D p)] [∀ p : AllPoints D,
    IsAdicComplete (IsLocalRing.maximalIdeal (localRing D p)) (localRing D p)] (he : ∀ p : AllPoints
    D, localException D p ∈ IsLocalRing.maximalIdeal (localRing D p)) (O : Type) [CommRing O]
    [Algebra O R] [∀ p : AllPoints D, Algebra O (localRing D p)] (hO : ∀ (p : AllPoints D) (o : O),
    localFromSurface D p (algebraMap O R o) = algebraMap O (localRing D p) o) :
    ∃ E : CurveOrderLimit R t x beta G ≃ₗ[O] childOrder D, ∀ (p : curveThreads R t x beta G)
      (r : R), (∀ j : ℕ, p.val j = surfaceToChartPair R t x r) → E (curveLimitMk R t x beta G p) =
      childOrderMap D r := by sorry
