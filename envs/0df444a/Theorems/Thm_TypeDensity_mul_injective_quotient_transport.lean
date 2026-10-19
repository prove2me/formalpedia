-- Prove2me | Theorems.Thm_TypeDensity_mul_injective_quotient_transport
-- name    : TypeDensity.mul_injective_quotient_transport
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:33.036867+00:00
-- url     : https://prove2.me/theorems/dd2f064e-bb74-4eac-a51d-70fd6cee6a48
-- title:
--   Transversality transports along a ring isomorphism `Θ` sending the parameter `e` to a unit multiple of `eT`: if multiplication by `e` is injective modulo `g`, then multiplication by `eT` is injective
-- statement:
--   Transversality transports along a ring isomorphism `Θ` sending the parameter `e` to a unit multiple of `eT`: if multiplication by `e` is injective modulo `g`, then multiplication by `eT` is injective modulo `Θ g`.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L859-L873

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
variable {S T : Type} [CommRing S] [CommRing T]

theorem TypeDensity.mul_injective_quotient_transport (Θ : S ≃+* T) {g e : S} {eT u : T} (hu : IsUnit u)
    (he : Θ e * u = eT)
    (h : Function.Injective
      (fun a : S ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g}) e * a)) :
    Function.Injective
      (fun a : T ⧸ Ideal.span {Θ g} => Ideal.Quotient.mk (Ideal.span {Θ g}) eT * a) := by sorry
