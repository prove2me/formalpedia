-- Prove2me | Theorems.Thm_TypeDensity_sum_allowedPatterns_crossing
-- name    : TypeDensity.sum_allowedPatterns_crossing
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:57.411058+00:00
-- url     : https://prove2.me/theorems/91504b0c-3daf-46e1-b2e7-4f96f7c738db
-- title:
--   Reindexing the allowed patterns of the crossing state `T(a,b;c,h)` by their data `(d, rt, rx)` and the off-boundary pattern of weight `d - rt - rx`.
-- statement:
--   The allowed patterns of the crossing state `T(a,b;c,h)` are reindexed by their data `(d, rt, rx)` and the off-boundary pattern of weight `d - rt - rx`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L603-L619

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_sum_allowedPatterns_reindex
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

theorem TypeDensity.sum_allowedPatterns_crossing (a b c h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (F : ℕ → ℕ → ℕ → Pattern (State.crossing a b c h).degree → Coef) :
    ∑ P ∈ allowedPatterns (State.crossing a b c h), F P.d.val P.rt.val P.rx.val P.other =
    ∑ d ∈ Finset.Icc 1 (min c h), ∑ rt ∈ Finset.range (d + 1), ∑ rx ∈ Finset.range (d + 1),
      (if ((0 < rt ↔ d < c) ∧ (0 < rx ↔ d < h) ∧ rt + rx ≤ d) then
        ∑ m ∈ (Finset.univ : Finset (Pattern (State.crossing a b c h).degree)).filter
          (fun m ↦ patternWeight m = d - rt - rx), F d rt rx m
      else 0) := by sorry
