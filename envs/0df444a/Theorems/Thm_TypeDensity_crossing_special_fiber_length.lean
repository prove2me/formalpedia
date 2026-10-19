-- Prove2me | Theorems.Thm_TypeDensity_crossing_special_fiber_length
-- name    : TypeDensity.crossing_special_fiber_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:45.33598+00:00
-- url     : https://prove2.me/theorems/fcc746d2-b4a3-4260-b922-9c12f20fdfc1
-- title:
--   A principal quotient of `k[[T,X]]/(T^a X^b)` (with `a, b > 0`) by `f` has length `a c + b h`, where `c` and `h` are the contacts of `f` with `T` and with `X`.
-- statement:
--   A principal quotient of `k[[T,X]]/(T^a X^b)` (with `a, b > 0`) by `f` has length `a c + b h`, where `c` and `h` are the contacts of `f` with `T` and with `X`.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L64-L78

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_length_double_quotient_eq
import Theorems.Thm_TypeDensity_length_quotient_sup_mul_eq_add
import Theorems.Thm_TypeDensity_axis_contact
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.crossing_special_fiber_length (k : Type) [Field k] (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : SpecialFiber k a b) (ht : contact f (fiberT k a b) = c)
    (hx : contact f (fiberX k a b) = h) :
    Module.length (SpecialFiber k a b) ((SpecialFiber k a b) ⧸ Ideal.span {f}) = a * c + b * h := by sorry
