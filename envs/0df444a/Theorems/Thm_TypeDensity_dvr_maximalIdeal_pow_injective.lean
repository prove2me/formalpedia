-- Prove2me | Theorems.Thm_TypeDensity_dvr_maximalIdeal_pow_injective
-- name    : TypeDensity.dvr_maximalIdeal_pow_injective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:28.95073+00:00
-- url     : https://prove2.me/theorems/b4f9b84b-8942-4138-803a-376be96bbb47
-- title:
--   In a DVR, `n ↦ m^n` is injective.
-- statement:
--   In a DVR, `n ↦ m^n` is injective.
-- source:
--   TypeDensity/Unramified/Extension.lean#L483-L492

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.dvr_maximalIdeal_pow_injective (B : Type) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] (a b : ℕ)
    (h : (IsLocalRing.maximalIdeal B) ^ a = (IsLocalRing.maximalIdeal B) ^ b) :
    a = b := by sorry
