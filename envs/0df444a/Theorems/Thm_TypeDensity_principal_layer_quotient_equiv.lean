-- Prove2me | Theorems.Thm_TypeDensity_principal_layer_quotient_equiv
-- name    : TypeDensity.principal_layer_quotient_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:37.399672+00:00
-- url     : https://prove2.me/theorems/2aa9dc52-9649-4912-8f14-6806a929b782
-- title:
--   If `e` is a nonzerodivisor, the layer map induces an `A`-linear isomorphism from `A ⧸ (e)` onto the principal layer `(e)^j ⧸ (e)^(j+1)`.
-- statement:
--   If `e` is a nonzerodivisor, the layer map induces an `A`-linear isomorphism from `A ⧸ (e)` onto the principal layer `(e)^j ⧸ (e)^(j+1)`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L739-L750

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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.principal_layer_quotient_equiv (A : Type) [CommRing A] (e : A) (j : ℕ)
    (he : Function.Injective (fun a : A ↦ e*a)) :
    ∃ L : (A ⧸ Ideal.span {e}) ≃ₗ[A] PrincipalLayer A e j, ∀ a : A,
    (L (Ideal.Quotient.mk (Ideal.span {e}) a)).val = principalLayerMap A e j a := by sorry
