-- Prove2me | Theorems.Thm_TypeDensity_projectiveNormalizer_rational_ne_zero
-- name    : TypeDensity.projectiveNormalizer_rational_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:42.792262+00:00
-- url     : https://prove2.me/theorems/84d6a532-1dd4-4830-ac21-0091544fcd5b
-- title:
--   The projective normalizer is a nonzero rational function.
-- statement:
--   The projective normalizer is a nonzero rational function.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L430-L438

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_rational_projectiveNormalizer
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

theorem TypeDensity.projectiveNormalizer_rational_ne_zero (n : ℕ) : (projectiveNormalizer n).rational ≠ 0 := by sorry
