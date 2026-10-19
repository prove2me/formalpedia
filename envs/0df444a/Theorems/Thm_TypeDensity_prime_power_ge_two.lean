-- Prove2me | Theorems.Thm_TypeDensity_prime_power_ge_two
-- name    : TypeDensity.prime_power_ge_two
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:12.132415+00:00
-- url     : https://prove2.me/theorems/cc5ef53c-f05e-4d65-8d53-a9c6ba3b7d93
-- title:
--   A prime power is at least `2`.
-- statement:
--   A prime power is at least `2`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L159-L163

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.prime_power_ge_two (q : ℕ) (hq : PrimePower q) :
    2 ≤ q := by sorry
