-- Prove2me | Theorems.Thm_TypeDensity_crossingQ_eq_qmul_qplus_qdiag_qminus
-- name    : TypeDensity.crossingQ_eq_qmul_qplus_qdiag_qminus
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:14.73634+00:00
-- url     : https://prove2.me/theorems/07e3cd2b-699d-429b-b199-9c3d38ba1033
-- title:
--   **Crossing factorization.** `U_{a,b} = U_{a+b,b}⁺ · J(P_{a+b}) · U_{a,a+b}⁻`, where `J` is the diagonal substitution and `P_{a+b} = eulerSer (-1) (a+b)`.
-- statement:
--   **Crossing factorization.** `U_{a,b} = U_{a+b,b}⁺ · J(P_{a+b}) · U_{a,a+b}⁻`, where `J` is the diagonal substitution and `P_{a+b} = eulerSer (-1) (a+b)`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L833-L850

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_state_law_unfold
import Theorems.Thm_TypeDensity_chooseTwo_add
import Theorems.Thm_TypeDensity_qpow_zero
import Theorems.Thm_TypeDensity_X_sub_one_mul_crossingWeight
import Theorems.Thm_TypeDensity_qmul_qplus_qdiag_qminus_apply
import Theorems.Thm_TypeDensity_patternSum_eq_of_le
import Theorems.Thm_TypeDensity_lawCoef_exitLaw_crossing
import Theorems.Thm_TypeDensity_lawCoef_stateLaw_crossing_comm
import Theorems.Thm_TypeDensity_crossingQ_zero_zero
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_sum_triple_reindex
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_coeff_zero_eulerSer
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_rational_eminusOne
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_scalar_one
import Theorems.Thm_TypeDensity_QPositive_qmul
import Theorems.Thm_TypeDensity_QPositive_qplus
import Theorems.Thm_TypeDensity_QPositive_qminus
import Theorems.Thm_TypeDensity_qPositive_qdiag
import Theorems.Thm_TypeDensity_qmul_zero_zero
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

theorem TypeDensity.crossingQ_eq_qmul_qplus_qdiag_qminus (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b) :
    crossingQ a b c h = qmul (qmul (qplus (crossingQ (a + b) b)) (qdiag (eulerSer (-1) (a + b))))
        (qminus (crossingQ a (a + b))) c h := by sorry
