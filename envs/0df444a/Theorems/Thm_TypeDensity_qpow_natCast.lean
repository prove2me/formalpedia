-- Prove2me | Theorems.Thm_TypeDensity_qpow_natCast
-- name    : TypeDensity.qpow_natCast
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:51.960516+00:00
-- url     : https://prove2.me/theorems/5d07bcaf-a015-4342-8ad4-203f370affae
-- title:
--   `q^n` for natural `n` is the scalar `X^n`.
-- statement:
--   `q^n` for natural `n` is the scalar `X^n`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L150-L152

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.qpow_natCast (n : ℕ) : qpow (n : ℤ) = scalar ((RatFunc.X : RatFunc ℚ) ^ n) := by sorry
