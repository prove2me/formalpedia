-- Prove2me | Theorems.Thm_TypeDensity_global_coefficients_safe
-- name    : TypeDensity.global_coefficients_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:18.404008+00:00
-- url     : https://prove2.me/theorems/6d13ac6c-ae18-4628-8bff-d263df534e6d
-- title:
--   The coefficients of the monic and projective global laws are safe.
-- statement:
--   The coefficients of the monic and projective global laws are safe.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L563-L573

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_sum_safe
import Theorems.Thm_TypeDensity_global_law_safe
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

theorem TypeDensity.global_coefficients_safe (n : ℕ) (σ : FactorType) :
    (monicExpr n σ).allSafe ∧ (projectiveExpr n σ).allSafe := by sorry
