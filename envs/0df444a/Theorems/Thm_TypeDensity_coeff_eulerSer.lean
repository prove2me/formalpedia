-- Prove2me | Theorems.Thm_TypeDensity_coeff_eulerSer
-- name    : TypeDensity.coeff_eulerSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:56.040149+00:00
-- url     : https://prove2.me/theorems/d42eb3bf-e372-4064-903f-4c9b6b13d0be
-- title:
--   The `n`-th coefficient of the Euler transform `eulerSer ε a` is the pattern sum `patternSum ε a n n`.
-- statement:
--   The `n`-th coefficient of the Euler transform `eulerSer ε a` is the pattern sum `patternSum ε a n n`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L696-L702

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_adamsRat_X
import Theorems.Thm_TypeDensity_coeff_adamsSer
import Theorems.Thm_TypeDensity_constantCoeff_adamsSer
import Theorems.Thm_TypeDensity_expSer_zero
import Theorems.Thm_TypeDensity_constantCoeff_logSer
import Theorems.Thm_TypeDensity_expSer_add
import Theorems.Thm_TypeDensity_prod_formalPow_adamsSer_clusterSer_scongr
import Theorems.Thm_TypeDensity_Expr_wf_pow
import Theorems.Thm_TypeDensity_Expr_rational_add
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_Expr_rational_sum
import Theorems.Thm_TypeDensity_Expr_rational_pow
import Theorems.Thm_TypeDensity_coeff_euler_families_eq_patternSum
import Theorems.Thm_TypeDensity_adamsCoef_scalar
import Theorems.Thm_TypeDensity_adamsCoef_adamsCoef
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
import Theorems.Thm_TypeDensity_scalar_mul_eq_smul
import Theorems.Thm_TypeDensity_rat_smul_eq_scalar_mul
import Theorems.Thm_TypeDensity_adamsSer_logSer
import Theorems.Thm_TypeDensity_sum_divisors_sum_divisors_div
import Theorems.Thm_TypeDensity_sum_divisors_moebius
import Theorems.Thm_TypeDensity_SCongr_expSer
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

theorem TypeDensity.coeff_eulerSer (ε : ℤ) (a n : ℕ) :
    PowerSeries.coeff n (eulerSer ε a) = patternSum ε a n n := by sorry
