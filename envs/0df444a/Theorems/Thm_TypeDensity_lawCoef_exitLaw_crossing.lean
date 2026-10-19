-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_exitLaw_crossing
-- name    : TypeDensity.lawCoef_exitLaw_crossing
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:16.027982+00:00
-- url     : https://prove2.me/theorems/65b62210-f8f0-4b2b-80c8-7aa9740e40b9
-- title:
--   The exit law of `T(a,b;c,h)` regrouped by divisor degree `d` and tangent depths `rt`, `rx` into crossing-child laws and pattern sums `patternSum (-1) (a+b) (ac+bh) (d-rt-rx)`.
-- statement:
--   The exit law of `T(a,b;c,h)` is regrouped by divisor degree `d` and tangent depths `rt`, `rx` into crossing-child laws and pattern sums `patternSum (-1) (a+b) (ac+bh) (d-rt-rx)`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L315-L347

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_adamsRat_X
import Theorems.Thm_TypeDensity_sum_allowedPatterns_crossing
import Theorems.Thm_TypeDensity_lawWf_stateLaw
import Theorems.Thm_TypeDensity_wf_subst_and_rational_subst
import Theorems.Thm_TypeDensity_lawCoef_otherChildren
import Theorems.Thm_TypeDensity_sum_patterns_scalar_mul_eq_patternSum
import Theorems.Thm_TypeDensity_Expr_wf_pow
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_lawCoef_lawScale
import Theorems.Thm_TypeDensity_lawCoef_flatMap
import Theorems.Thm_TypeDensity_lawCoef_lawProd
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_adamsCoef_single
import Theorems.Thm_TypeDensity_adamsCoef_one
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

theorem TypeDensity.lawCoef_exitLaw_crossing (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) :
    lawCoef (exitLaw (State.crossing a b c h)) = ∑ d ∈ Finset.Icc 1 (min c h),
        ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
        (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then scalar
        (divisorProbability (State.crossing a b c h) d).rational *
        ((if rt = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) a rt (c - d)))) *
        (if rx = 0 then 1 else lawCoef (stateLaw (State.crossing (a + b) b rx (h - d)))) *
        patternSum (-1) (a + b) (a * c + b * h) (d - rt - rx)) else 0) := by sorry
