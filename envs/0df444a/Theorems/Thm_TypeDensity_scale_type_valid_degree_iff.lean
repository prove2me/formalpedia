-- Prove2me | Theorems.Thm_TypeDensity_scale_type_valid_degree_iff
-- name    : TypeDensity.scale_type_valid_degree_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:06.507908+00:00
-- url     : https://prove2.me/theorems/61116427-897d-45fe-84ca-33d4a29ea53c
-- title:
--   Scaling by `δ > 0` is injective on types, preserves validity, and multiplies the degree by `δ`.
-- statement:
--   Scaling by `δ > 0` is injective on types, preserves validity, and multiplies the degree by `δ`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L595-L609

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
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

theorem TypeDensity.scale_type_valid_degree_iff (δ r : ℕ) (hδ : 0 < δ) (τ : FactorType) :
    ((ValidType (scaleType δ τ) ∧ typeDegree (scaleType δ τ) = δ * r) ↔
      (ValidType τ ∧ typeDegree τ = r)) ∧ Function.Injective (scaleType δ) := by sorry
