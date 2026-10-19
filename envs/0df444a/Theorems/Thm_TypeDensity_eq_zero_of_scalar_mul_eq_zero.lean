-- Prove2me | Theorems.Thm_TypeDensity_eq_zero_of_scalar_mul_eq_zero
-- name    : TypeDensity.eq_zero_of_scalar_mul_eq_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:13.630981+00:00
-- url     : https://prove2.me/theorems/c4e9c49f-76d2-4abf-81f1-a457d709482a
-- title:
--   `scalar w * x = 0` forces `x = 0` when `w ≠ 0`.
-- statement:
--   `scalar w * x = 0` forces `x = 0` when `w ≠ 0`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L835-L838

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_scalar_mul_left_cancel
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

theorem TypeDensity.eq_zero_of_scalar_mul_eq_zero {w : RatFunc ℚ} (hw : w ≠ 0) {x : Coef}
    (h : scalar w * x = 0) : x = 0 := by sorry
