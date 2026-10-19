-- Prove2me | Theorems.Thm_TypeDensity_recipCoef_lawCoef_globalLaw_true
-- name    : TypeDensity.recipCoef_lawCoef_globalLaw_true
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:55:58.718244+00:00
-- url     : https://prove2.me/theorems/a17dfe8a-4d5b-470a-9e63-a9942262c5bc
-- title:
--   **Projective self-reciprocity.** The normalised global projective law `R_n` is invariant under reciprocal substitution: `R_n(1/q) = R_n(q)` as elements of `Coef`.
-- statement:
--   **Projective self-reciprocity.** The normalised global projective law `R_n` is invariant under reciprocal substitution: `R_n(1/q) = R_n(q)` as elements of `Coef`.
-- source:
--   TypeDensity/Reciprocity/Main.lean#L236-L276

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_cluster_reciprocity
import Theorems.Thm_TypeDensity_lawCoef_globalLaw_true
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_constantCoeff_pPow
import Theorems.Thm_TypeDensity_pPow_pPow
import Theorems.Thm_TypeDensity_constantCoeff_clusterSer
import Theorems.Thm_TypeDensity_recipCoef_scalar
import Theorems.Thm_TypeDensity_scalar_mul
import Theorems.Thm_TypeDensity_scalar_one
import Theorems.Thm_TypeDensity_recipRat_projectiveNormalizer
import Theorems.Thm_TypeDensity_projectiveNormalizer_rational_ne_zero
import Theorems.Thm_TypeDensity_coeff_recipSer
import Theorems.Thm_TypeDensity_coeff_codilate
import Theorems.Thm_TypeDensity_codilate_dilate
import Theorems.Thm_TypeDensity_codilate_pPow
import Theorems.Thm_TypeDensity_recipSer_pPow
import Theorems.Thm_TypeDensity_scalar_mul_left_cancel
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

theorem TypeDensity.recipCoef_lawCoef_globalLaw_true (n : ℕ) :
    recipCoef (lawCoef (globalLaw true n)) = lawCoef (globalLaw true n) := by sorry
