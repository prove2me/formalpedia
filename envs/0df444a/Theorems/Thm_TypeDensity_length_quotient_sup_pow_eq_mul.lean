-- Prove2me | Theorems.Thm_TypeDensity_length_quotient_sup_pow_eq_mul
-- name    : TypeDensity.length_quotient_sup_pow_eq_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:50.316083+00:00
-- url     : https://prove2.me/theorems/7bf3bbfd-5d84-427d-b081-40a68b4c7e91
-- title:
--   If `t` is a nonzerodivisor modulo `I`, then `ℓ(R/(I + (tⁿ))) = n · ℓ(R/(I + (t)))`.
-- statement:
--   If `t` is a nonzerodivisor modulo `I`, then `ℓ(R/(I + (tⁿ))) = n · ℓ(R/(I + (t)))`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1241-L1256

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_length_quotient_sup_mul_eq_add
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

theorem TypeDensity.length_quotient_sup_pow_eq_mul (R : Type) [CommRing R] (I : Ideal R) (t : R)
    (ht : ∀ x, t * x ∈ I → x ∈ I) (n : ℕ) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {t ^ n})) = (n : ℕ∞) *
    Module.length R (R ⧸ (I ⊔ Ideal.span {t})) := by sorry
