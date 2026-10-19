-- Prove2me | Theorems.Thm_TypeDensity_rational_divisorProbability_single
-- name    : TypeDensity.rational_divisorProbability_single
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:48.088323+00:00
-- url     : https://prove2.me/theorems/d5ab2dae-dfa3-4261-9ef0-7b58189eac0a
-- title:
--   The divisor probability of `S(a;c)` at degree `d` is `q^{-tri d} (q-1)^{[d < c]}`.
-- statement:
--   The divisor probability of `S(a;c)` at degree `d` is `q^{-tri d} (q-1)^{[d < c]}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L410-L416

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_rational_eminusOne
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.rational_divisorProbability_single (a c d : ℕ) :
    (divisorProbability (State.single a c) d).rational =
      ((RatFunc.X : RatFunc ℚ) ^ tri d)⁻¹ *
        ((RatFunc.X : RatFunc ℚ) - 1) ^ (if d < c then 1 else 0) := by sorry
