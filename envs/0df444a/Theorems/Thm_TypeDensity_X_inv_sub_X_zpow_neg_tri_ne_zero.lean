-- Prove2me | Theorems.Thm_TypeDensity_X_inv_sub_X_zpow_neg_tri_ne_zero
-- name    : TypeDensity.X_inv_sub_X_zpow_neg_tri_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:34.561002+00:00
-- url     : https://prove2.me/theorems/0e29a988-1d36-4873-8c66-cef2a21bcf2c
-- title:
--   For `n ≥ 2`, the scalar `q⁻¹ - q^{-tri n}` is nonzero.
-- statement:
--   For `n ≥ 2`, the scalar `q⁻¹ - q^{-tri n}` is nonzero.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L487-L492

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_rational_returnWeight
import Theorems.Thm_TypeDensity_one_sub_rational_returnWeight_ne_zero
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

theorem TypeDensity.X_inv_sub_X_zpow_neg_tri_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    (RatFunc.X : RatFunc ℚ)⁻¹ - (RatFunc.X : RatFunc ℚ) ^ (-(tri n : ℤ)) ≠ 0 := by sorry
