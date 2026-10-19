-- Prove2me | Theorems.Thm_TypeDensity_rational_projectiveNormalizer
-- name    : TypeDensity.rational_projectiveNormalizer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:55.823545+00:00
-- url     : https://prove2.me/theorems/36cd7131-4f16-4c47-8afe-17d420233607
-- title:
--   The projective normalizer is `[n+1]_q = 1 + q + ⋯ + qⁿ`.
-- statement:
--   The projective normalizer is `[n+1]_q = 1 + q + ⋯ + qⁿ`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L401-L415

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.rational_projectiveNormalizer (n : ℕ) :
    (projectiveNormalizer n).rational =
      ∑ i ∈ Finset.range (n + 1), (RatFunc.X : RatFunc ℚ) ^ i := by sorry
