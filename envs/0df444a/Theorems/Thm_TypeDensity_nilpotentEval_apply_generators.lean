-- Prove2me | Theorems.Thm_TypeDensity_nilpotentEval_apply_generators
-- name    : TypeDensity.nilpotentEval_apply_generators
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:24.772995+00:00
-- url     : https://prove2.me/theorems/65170a8f-641b-458a-8b23-b9085c2ef0b2
-- title:
--   Values of `nilpotentEval` on constants and on the two variables.
-- statement:
--   `nilpotentEval φ e z` restricts to `φ` on constants and sends `T ↦ e` and `X ↦ z`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L239-L253

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.nilpotentEval_apply_generators (O S : Type) [CommRing O] [CommRing S] (φ : O →+* S)
    (e z : S) (he : IsNilpotent e) (hz : IsNilpotent z) :
    (∀ c : O, nilpotentEval φ e z he hz (MvPowerSeries.C c) = φ c) ∧
    nilpotentEval φ e z he hz (axisT O) = e ∧ nilpotentEval φ e z he hz (axisX O) = z := by sorry
