-- Prove2me | Theorems.Thm_TypeDensity_rational_divisorCount
-- name    : TypeDensity.rational_divisorCount
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:32.607087+00:00
-- url     : https://prove2.me/theorems/7617cef9-8b45-426c-9d7d-1d6c47ecf584
-- title:
--   The rational function of the divisor count of a pattern `m`: a product over rows `i` of generalized binomial coefficients in `availablePoints ε (i+1)`.
-- statement:
--   The rational function of the divisor count of a pattern `m` is a product over rows `i` of generalized binomial coefficients in `availablePoints ε (i+1)`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L933-L966

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_wf_pow
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_sub
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

theorem TypeDensity.rational_divisorCount (N : ℕ) (ε : ℤ) (m : Pattern N) :
    (divisorCount ε m).rational = ∏ i : Fin N, ((∏ j ∈ Finset.range (∑ j : Fin N, (m (i, j)).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C (1 / (∏ j : Fin N, ((Nat.factorial (m (i, j)).val : ℕ) : ℚ)))) := by sorry
