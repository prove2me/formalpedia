-- Prove2me | Theorems.Thm_TypeDensity_sum_divisors_sum_divisors_div
-- name    : TypeDensity.sum_divisors_sum_divisors_div
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:59.04099+00:00
-- url     : https://prove2.me/theorems/81b2b4b1-62c7-441d-ad55-85adbcd2e866
-- title:
--   Reindexing a double divisor sum: pairs `(k, j)` with `k ∣ n`, `j ∣ n/k` correspond to pairs `(m, k)` with `m ∣ n`, `k ∣ m` via `m = kj`.
-- statement:
--   Reindexing a double divisor sum: pairs `(k, j)` with `k ∣ n`, `j ∣ n/k` correspond to pairs `(m, k)` with `m ∣ n`, `k ∣ m` via `m = kj`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L236-L276

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

theorem TypeDensity.sum_divisors_sum_divisors_div {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → M) :
    ∑ k ∈ n.divisors, ∑ j ∈ (n / k).divisors, F k j
      = ∑ m ∈ n.divisors, ∑ k ∈ m.divisors, F k (m / k) := by sorry
