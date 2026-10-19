-- Prove2me | Theorems.Thm_TypeDensity_recipRat_projectiveNormalizer
-- name    : TypeDensity.recipRat_projectiveNormalizer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:07.663176+00:00
-- url     : https://prove2.me/theorems/557dd41c-1cce-47ce-9db4-6cd1d8d1274b
-- title:
--   `v([n+1]_q) = q⁻ⁿ [n+1]_q`.
-- statement:
--   `v([n+1]_q) = q⁻ⁿ [n+1]_q`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L417-L428

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_X
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

theorem TypeDensity.recipRat_projectiveNormalizer (n : ℕ) :
    recipRat (projectiveNormalizer n).rational =
      (RatFunc.X ^ n)⁻¹ * (projectiveNormalizer n).rational := by sorry
