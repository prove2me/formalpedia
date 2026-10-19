-- Prove2me | Theorems.Thm_TypeDensity_coeff_one_eulerSer_zero
-- name    : TypeDensity.coeff_one_eulerSer_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:01:25.82758+00:00
-- url     : https://prove2.me/theorems/3de1ef2b-5731-4162-8a46-8244d142f650
-- title:
--   The degree-one coefficient of `G_a = eulerSer 0 a` is `q Z_{a,1}`.
-- statement:
--   The degree-one coefficient of `G_a = eulerSer 0 a` is `q Z_{a,1}`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L900-L932

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_Expr_rational_add
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_coeff_succ_clusterSer
import Theorems.Thm_TypeDensity_coeff_one_clusterSer
import Theorems.Thm_TypeDensity_rational_divisorCount
import Theorems.Thm_TypeDensity_adamsCoef_one
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
import Theorems.Thm_TypeDensity_qpow_one
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

theorem TypeDensity.coeff_one_eulerSer_zero (a : ℕ) :
    PowerSeries.coeff 1 (eulerSer 0 a) = qpow 1 * AddMonoidAlgebra.single ({(a, 1)} : FactorType)
        1 := by sorry
