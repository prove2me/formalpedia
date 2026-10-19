-- Prove2me | Theorems.Thm_TypeDensity_global_law_safe
-- name    : TypeDensity.global_law_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:16.804339+00:00
-- url     : https://prove2.me/theorems/cc351b9c-17a2-4b87-9e8d-0d50a4fb68c6
-- title:
--   The global law (monic for `ε = false`, projective for `ε = true`) of degree `n` is safe.
-- statement:
--   The global law (monic for `ε = false`, projective for `ε = true`) of degree `n` is safe.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L539-L561

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_pow_safe
import Theorems.Thm_TypeDensity_expression_sum_safe
import Theorems.Thm_TypeDensity_projective_normalizer_positive
import Theorems.Thm_TypeDensity_divisor_count_safe
import Theorems.Thm_TypeDensity_law_safe_descend
import Theorems.Thm_TypeDensity_law_safe_mul
import Theorems.Thm_TypeDensity_law_safe_scale
import Theorems.Thm_TypeDensity_local_law_safe
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.global_law_safe (n : ℕ) (ε : Bool) :
    LawSafe (globalLaw ε n) := by sorry
