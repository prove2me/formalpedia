-- Prove2me | Theorems.Thm_TypeDensity_length_double_quotient_eq
-- name    : TypeDensity.length_double_quotient_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:49.216032+00:00
-- url     : https://prove2.me/theorems/dc9d2d47-938d-4f32-96b4-c40d126553fc
-- title:
--   Length of `(A/J)/I(A/J)` over `A/J` equals the length of `A/(J + I)` over `A`.
-- statement:
--   Length of `(A/J)/I(A/J)` over `A/J` equals the length of `A/(J + I)` over `A`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1175-L1183

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

theorem TypeDensity.length_double_quotient_eq (A : Type) [CommRing A] (J I : Ideal A) :
    Module.length (A ⧸ J) ((A ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) I) =
    Module.length A (A ⧸ (J ⊔ I)) := by sorry
