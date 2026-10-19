-- Prove2me | Theorems.Thm_TypeDensity_isDomain_of_regular_prime_element
-- name    : TypeDensity.isDomain_of_regular_prime_element
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:24.028524+00:00
-- url     : https://prove2.me/theorems/325f8171-13d9-4387-ba76-49e5840a6ca8
-- title:
--   A nontrivial ring with a nonzerodivisor `e` generating a prime ideal and with `⋂ₙ (e)ⁿ = 0` is a domain.
-- statement:
--   A nontrivial ring with a nonzerodivisor `e` generating a prime ideal and with `⋂ₙ (e)ⁿ = 0` is a domain.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1135-L1171

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.isDomain_of_regular_prime_element (A : Type) [CommRing A] [Nontrivial A] (e : A)
    (he : Function.Injective (fun a : A ↦ e * a)) (hprime : (Ideal.span {e}).IsPrime)
    (hinf : (⨅ n : ℕ, (Ideal.span {e})^n) = ⊥) :
    IsDomain A := by sorry
