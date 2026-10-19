-- Prove2me | Theorems.Thm_TypeDensity_single_special_fiber_length
-- name    : TypeDensity.single_special_fiber_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:43.977984+00:00
-- url     : https://prove2.me/theorems/e5add8a2-bedb-4efe-a08f-d6002e8c3f9b
-- title:
--   A principal quotient of `k[[T,X]]/(T^a)` (with `a > 0`) by `f` has length `a c`, where `c` is the contact of `f` with `T`.
-- statement:
--   A principal quotient of `k[[T,X]]/(T^a)` (with `a > 0`) by `f` has length `a c`, where `c` is the contact of `f` with `T`.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L80-L90

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

theorem TypeDensity.single_special_fiber_length (k : Type) [Field k] (a c : ℕ) (ha : 0 < a)
    (f : SpecialFiber k a 0) (hf : contact f (fiberT k a 0) = c) :
    Module.length (SpecialFiber k a 0) ((SpecialFiber k a 0) ⧸ Ideal.span {f}) = a * c := by sorry
