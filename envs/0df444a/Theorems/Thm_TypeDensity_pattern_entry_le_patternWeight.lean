-- Prove2me | Theorems.Thm_TypeDensity_pattern_entry_le_patternWeight
-- name    : TypeDensity.pattern_entry_le_patternWeight
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:45.499137+00:00
-- url     : https://prove2.me/theorems/0b900792-17fb-4801-859d-25f7feaf6748
-- title:
--   Each entry of a pattern is bounded by its weight.
-- statement:
--   Each entry of a pattern is bounded by its weight.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L638-L641

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
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

theorem TypeDensity.pattern_entry_le_patternWeight (N : ℕ) (m : Pattern N) (ij : Fin N × Fin N) :
    (m ij).val ≤ patternWeight m := by sorry
