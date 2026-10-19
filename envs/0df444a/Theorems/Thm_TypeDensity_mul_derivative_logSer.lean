-- Prove2me | Theorems.Thm_TypeDensity_mul_derivative_logSer
-- name    : TypeDensity.mul_derivative_logSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:46.753778+00:00
-- url     : https://prove2.me/theorems/ee168b64-4c9a-4715-8852-9d6afd0de307
-- title:
--   The logarithmic derivative `g · (log g)' = g'` (for `g(0) = 1`).
-- statement:
--   For `g(0) = 1`, the logarithmic derivative `g · (log g)' = g'` holds.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L450-L472

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

theorem TypeDensity.mul_derivative_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    g * PowerSeries.derivative Coef (logSer g) = PowerSeries.derivative Coef g := by sorry
