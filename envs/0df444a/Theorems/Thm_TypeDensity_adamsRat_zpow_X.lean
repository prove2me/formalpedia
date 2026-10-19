-- Prove2me | Theorems.Thm_TypeDensity_adamsRat_zpow_X
-- name    : TypeDensity.adamsRat_zpow_X
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:47.171534+00:00
-- url     : https://prove2.me/theorems/4c8180c6-50d8-4664-b43f-1c924e7e456c
-- title:
--   `ψ_δ (q^j) = q^{δj}` for integer `j`.
-- statement:
--   `ψ_δ (q^j) = q^{δj}` for integer `j`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L338-L341

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_adamsRat_X
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

theorem TypeDensity.adamsRat_zpow_X (δ : ℕ) (hδ : 0 < δ) (j : ℤ) :
    adamsRat δ ((RatFunc.X : RatFunc ℚ) ^ j) = (RatFunc.X : RatFunc ℚ) ^ ((δ : ℤ) * j) := by sorry
