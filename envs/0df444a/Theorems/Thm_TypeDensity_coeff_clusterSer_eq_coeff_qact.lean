-- Prove2me | Theorems.Thm_TypeDensity_coeff_clusterSer_eq_coeff_qact
-- name    : TypeDensity.coeff_clusterSer_eq_coeff_qact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:12.042194+00:00
-- url     : https://prove2.me/theorems/6be77d5c-1ffb-4942-83b9-769ec12cb1f1
-- title:
--   **Operator equation.** The cluster series is obtained from its Euler transform by the Gaussian twist and the contact representation: `B_a = ρ(U_{a,a}) Φ(G_a)`, coefficientwise.
-- statement:
--   **Operator equation.** The cluster series is obtained from its Euler transform by the Gaussian twist and the contact representation: `B_a = ρ(U_{a,a}) Φ(G_a)`, coefficientwise.
-- source:
--   TypeDensity/Reciprocity/Main.lean#L92-L141

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_state_law_unfold
import Theorems.Thm_TypeDensity_patternSum_eq_of_le
import Theorems.Thm_TypeDensity_sum_patterns_scalar_mul_eq_patternSum
import Theorems.Thm_TypeDensity_lawCoef_single_term
import Theorems.Thm_TypeDensity_rational_divisorProbability_single
import Theorems.Thm_TypeDensity_rational_returnWeight
import Theorems.Thm_TypeDensity_one_sub_rational_returnWeight_ne_zero
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_coeff_one_eulerSer_zero
import Theorems.Thm_TypeDensity_coeff_qact_crossingQ_gaussPhi_eulerSer
import Theorems.Thm_TypeDensity_lawCoef_single_self_term
import Theorems.Thm_TypeDensity_sum_allowedPatterns_single
import Theorems.Thm_TypeDensity_exists_unique_selfPattern_single
import Theorems.Thm_TypeDensity_wf_returnWeight
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_lawCoef_nil
import Theorems.Thm_TypeDensity_lawCoef_lawScale
import Theorems.Thm_TypeDensity_lawCoef_flatMap
import Theorems.Thm_TypeDensity_coeff_zero_clusterSer
import Theorems.Thm_TypeDensity_coeff_succ_clusterSer
import Theorems.Thm_TypeDensity_coeff_one_clusterSer
import Theorems.Thm_TypeDensity_Expr_rational_sub
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
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

theorem TypeDensity.coeff_clusterSer_eq_coeff_qact (a n : ℕ) (ha : 0 < a) :
    PowerSeries.coeff n (clusterSer a) =
      PowerSeries.coeff n (qact (crossingQ a a) (gaussPhi (eulerSer 0 a))) := by sorry
