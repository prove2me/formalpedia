-- Prove2me | Theorems.Thm_TypeDensity_X_sub_one_mul_crossingWeight
-- name    : TypeDensity.X_sub_one_mul_crossingWeight
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:44.711564+00:00
-- url     : https://prove2.me/theorems/45be7a44-1260-468b-b232-0b9d2f476003
-- title:
--   `(q-1) · w_j = (q-1)^j` for the crossing weight `w_0 = (q-1)⁻¹`, `w_j = (q-1)^{j-1}`.
-- statement:
--   `(q-1) · w_j = (q-1)^j` for the crossing weight `w_0 = (q-1)⁻¹`, `w_j = (q-1)^{j-1}`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L625-L631

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
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

theorem TypeDensity.X_sub_one_mul_crossingWeight (j : ℕ) :
    (RatFunc.X - 1) * (if j = 0 then (RatFunc.X - 1 : RatFunc ℚ)⁻¹ else (RatFunc.X - 1) ^ (j - 1))
      = (RatFunc.X - 1) ^ j := by sorry
