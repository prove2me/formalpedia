-- Prove2me | Theorems.Thm_TypeDensity_length_quotient_sup_mul_eq_add
-- name    : TypeDensity.length_quotient_sup_mul_eq_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:48.65598+00:00
-- url     : https://prove2.me/theorems/d58b26b1-05c1-4204-821c-28b289ea2fb8
-- title:
--   If `s` is a nonzerodivisor modulo `I`, then `ℓ(R/(I + (t s))) = ℓ(R/(I + (t))) + ℓ(R/(I + (s)))`.
-- statement:
--   If `s` is a nonzerodivisor modulo `I`, then `ℓ(R/(I + (t s))) = ℓ(R/(I + (t))) + ℓ(R/(I + (s)))`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1185-L1239

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

theorem TypeDensity.length_quotient_sup_mul_eq_add (R : Type) [CommRing R] (I : Ideal R) (s t : R)
    (hs : ∀ x, s * x ∈ I → x ∈ I) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {t * s})) = Module.length R (R ⧸ (I ⊔ Ideal.span {t})) +
    Module.length R (R ⧸ (I ⊔ Ideal.span {s})) := by sorry
