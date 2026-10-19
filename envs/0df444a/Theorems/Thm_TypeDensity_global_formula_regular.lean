-- Prove2me | Theorems.Thm_TypeDensity_global_formula_regular
-- name    : TypeDensity.global_formula_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:26.982399+00:00
-- url     : https://prove2.me/theorems/56547c35-d4a8-4657-bf1e-f86745b83aea
-- title:
--   The global formula is regular at every prime power.
-- statement:
--   The global formula is regular at every prime power.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L575-L581

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_regular
import Theorems.Thm_TypeDensity_prime_power_ge_two
import Theorems.Thm_TypeDensity_global_coefficients_safe
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

theorem TypeDensity.global_formula_regular (n : ℕ) (σ : FactorType) :
    FormulaRegular n σ := by sorry
