-- Prove2me | Theorems.Thm_TypeDensity_two_mul_tri
-- name    : TypeDensity.two_mul_tri
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:11.323511+00:00
-- url     : https://prove2.me/theorems/4720e21e-1d66-458c-9aae-3fd0337a09c6
-- title:
--   `2 · tri n = n(n+1)`, as integers.
-- statement:
--   `2 · tri n = n(n+1)`, as integers.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L242-L246

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

theorem TypeDensity.two_mul_tri (n : ℕ) : 2 * (tri n : ℤ) = n * (n + 1) := by sorry
