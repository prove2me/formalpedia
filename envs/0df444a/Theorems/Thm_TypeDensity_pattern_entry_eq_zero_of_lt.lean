-- Prove2me | Theorems.Thm_TypeDensity_pattern_entry_eq_zero_of_lt
-- name    : TypeDensity.pattern_entry_eq_zero_of_lt
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:43.258428+00:00
-- url     : https://prove2.me/theorems/4fbc44f0-31ae-4682-bbda-e458a30e3ba2
-- title:
--   An entry `m(i,j)` of a pattern of weight `< (i+1)(j+1)` vanishes.
-- statement:
--   An entry `m(i,j)` of a pattern of weight `< (i+1)(j+1)` vanishes.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L643-L649

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

theorem TypeDensity.pattern_entry_eq_zero_of_lt (N : ℕ) (m : Pattern N) (ij : Fin N × Fin N)
    (h : patternWeight m < (ij.1.val + 1) * (ij.2.val + 1)) : (m ij).val = 0 := by sorry
