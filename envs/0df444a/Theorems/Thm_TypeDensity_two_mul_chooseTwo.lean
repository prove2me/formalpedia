-- Prove2me | Theorems.Thm_TypeDensity_two_mul_chooseTwo
-- name    : TypeDensity.two_mul_chooseTwo
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:10.003318+00:00
-- url     : https://prove2.me/theorems/aa2927a4-bca5-4129-be67-635ba8651601
-- title:
--   `2 · C(n,2) = n(n-1)`, as integers.
-- statement:
--   `2 · C(n,2) = n(n-1)`, as integers.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L248-L255

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

theorem TypeDensity.two_mul_chooseTwo (n : ℕ) : 2 * (chooseTwo n : ℤ) = n * (n - 1) := by sorry
