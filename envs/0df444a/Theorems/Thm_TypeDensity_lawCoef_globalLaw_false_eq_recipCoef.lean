-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_globalLaw_false_eq_recipCoef
-- name    : TypeDensity.lawCoef_globalLaw_false_eq_recipCoef
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:54:51.217238+00:00
-- url     : https://prove2.me/theorems/70f6b6df-a75f-48c3-bd5f-4bff2f604b55
-- title:
--   **Affine reciprocity.** The global monic law is the reciprocal of the root law: `F_global(q) = F_{S(1;n)}(1/q)` as elements of `Coef`.
-- statement:
--   **Affine reciprocity.** The global monic law is the reciprocal of the root law: `F_global(q) = F_{S(1;n)}(1/q)` as elements of `Coef`.
-- source:
--   TypeDensity/Reciprocity/Main.lean#L221-L234

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_cluster_reciprocity
import Theorems.Thm_TypeDensity_lawCoef_globalLaw_false
import Theorems.Thm_TypeDensity_coeff_eulerSer
import Theorems.Thm_TypeDensity_coeff_succ_clusterSer
import Theorems.Thm_TypeDensity_qpow_natCast
import Theorems.Thm_TypeDensity_qpow_neg_mul_qpow
import Theorems.Thm_TypeDensity_coeff_recipSer
import Theorems.Thm_TypeDensity_coeff_dilate
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

theorem TypeDensity.lawCoef_globalLaw_false_eq_recipCoef (n : ℕ) (hn : 0 < n) :
    lawCoef (globalLaw false n) = recipCoef (lawCoef (rootLaw n)) := by sorry
