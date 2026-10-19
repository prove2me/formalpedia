-- Prove2me | Theorems.Thm_TypeDensity_recipRat_recipRat
-- name    : TypeDensity.recipRat_recipRat
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:45.768411+00:00
-- url     : https://prove2.me/theorems/00fda548-1fd3-4d7e-bbaf-178e79806b15
-- title:
--   `q ↦ q⁻¹` is an involution of `ℚ(q)`.
-- statement:
--   `q ↦ q⁻¹` is an involution of `ℚ(q)`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L48-L52

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_algebraMap
import Theorems.Thm_TypeDensity_recipRat_C
import Theorems.Thm_TypeDensity_recipRat_X
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.recipRat_recipRat (f : RatFunc ℚ) : recipRat (recipRat f) = f := by sorry
