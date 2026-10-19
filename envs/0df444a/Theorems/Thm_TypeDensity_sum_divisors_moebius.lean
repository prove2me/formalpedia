-- Prove2me | Theorems.Thm_TypeDensity_sum_divisors_moebius
-- name    : TypeDensity.sum_divisors_moebius
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:05.219179+00:00
-- url     : https://prove2.me/theorems/4d9c9484-bd6c-42e5-8b73-5a4a18e82e9b
-- title:
--   `Σ_{k ∣ m} μ(k)` is `1` for `m = 1` and `0` otherwise.
-- statement:
--   `Σ_{k ∣ m} μ(k)` is `1` for `m = 1` and `0` otherwise.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L307-L313

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

theorem TypeDensity.sum_divisors_moebius (m : ℕ) :
    ∑ k ∈ m.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℚ) = if m = 1 then 1 else 0 := by sorry
