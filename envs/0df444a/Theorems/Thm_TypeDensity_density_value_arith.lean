-- Prove2me | Theorems.Thm_TypeDensity_density_value_arith
-- name    : TypeDensity.density_value_arith
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:15.815212+00:00
-- url     : https://prove2.me/theorems/04620eb0-1ad6-4d53-bb36-3c196a54b643
-- title:
--   Arithmetic of `densityValue` (multiplicativity, additivity, values on `q⁻ⁿ` and `1`, finiteness and positivity) and positivity of state volumes at an integer `q ≥ 2`.
-- statement:
--   Arithmetic of `densityValue` (multiplicativity, additivity, values on `q⁻ⁿ` and `1`, finiteness and positivity) and positivity of state volumes hold at an integer `q ≥ 2`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L333-L365

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

theorem TypeDensity.density_value_arith (q : ℕ) (hq : 2 ≤ q) (x y : Expr) (hx : 0 ≤ x.eval q)
    (hy : 0 ≤ y.eval q) (n : ℕ) (s : State) (hs : s.Valid) :
    densityValue (.mul x y) q = densityValue x q * densityValue y q ∧
      densityValue (.add x y) q = densityValue x q + densityValue y q ∧
      densityValue (.inv (.pow .var n)) q = (q : ℝ≥0∞)⁻¹ ^ n ∧
      densityValue (.const 1) q = 1 ∧ densityValue x q ≠ ⊤ ∧
      (0 < x.eval q → densityValue x q ≠ 0) ∧ 0 < (stateVolume s).eval q ∧
      (stateVolume s).eval q ≠ 0 := by sorry
