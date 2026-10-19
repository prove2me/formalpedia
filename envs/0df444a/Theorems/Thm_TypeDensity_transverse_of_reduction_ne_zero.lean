-- Prove2me | Theorems.Thm_TypeDensity_transverse_of_reduction_ne_zero
-- name    : TypeDensity.transverse_of_reduction_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:34.619656+00:00
-- url     : https://prove2.me/theorems/dec4037b-75a4-42d5-a799-5efa8043d036
-- title:
--   Let `e` be a non-zero-divisor of a noetherian local ring `S` with `S / (e) ≃ k[[X]]`, and let `g` have nonzero image in `k[[X]]`.
-- statement:
--   Let `e` be a non-zero-divisor of a noetherian local ring `S` with `S / (e) ≃ k[[X]]`, and let `g` have nonzero image in `k[[X]]`. Then `e` is a non-zero-divisor modulo `g`, `g` is a non-zero-divisor modulo `e`, and `(g, e)` contains a power of the maximal ideal.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L100-L150

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Unramified_Extension
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
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.transverse_of_reduction_ne_zero (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e g : S) (hereg : Function.Injective (fun y : S ↦ e * y)) (k : Type)
    [Field k] (q : (S ⧸ Ideal.span {e}) ≃+* PowerSeries k)
    (hg : q (Ideal.Quotient.mk (Ideal.span {e}) g) ≠ 0) :
    Function.Injective (fun a : S ⧸ Ideal.span {g} ↦ Ideal.Quotient.mk (Ideal.span {g}) e * a) ∧
      Function.Injective
        (fun a : S ⧸ Ideal.span {e} ↦ Ideal.Quotient.mk (Ideal.span {e}) g * a) ∧
      ∃ L : ℕ, (IsLocalRing.maximalIdeal S)^L ≤ Ideal.span {g, e} := by sorry
