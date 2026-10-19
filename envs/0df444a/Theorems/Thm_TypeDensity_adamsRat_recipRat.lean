-- Prove2me | Theorems.Thm_TypeDensity_adamsRat_recipRat
-- name    : TypeDensity.adamsRat_recipRat
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:49.755549+00:00
-- url     : https://prove2.me/theorems/ec87bfff-079d-4139-9d59-75042fa2bb85
-- title:
--   The Adams substitution commutes with `q ↦ q⁻¹`.
-- statement:
--   The Adams substitution commutes with `q ↦ q⁻¹`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L311-L319

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_recipRat_algebraMap
import Theorems.Thm_TypeDensity_adamsRat_X
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

theorem TypeDensity.adamsRat_recipRat (δ : ℕ) (hδ : 0 < δ) (f : RatFunc ℚ) :
    adamsRat δ (recipRat f) = recipRat (adamsRat δ f) := by sorry
