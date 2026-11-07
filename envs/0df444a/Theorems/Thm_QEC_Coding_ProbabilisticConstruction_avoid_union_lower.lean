-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_union_lower
-- name    : QEC.Coding.ProbabilisticConstruction.avoid_union_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:11.835001+00:00
-- url     : https://prove2.me/theorems/66e4a5f0-8e45-4ac1-8539-5982dbf75a6a
-- title:
--   Probabilistic Construction: avoid union lower
-- statement:
--   Multiply the one-event bounds along a finite extension of a conditioning set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L99-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L99-L116

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
include hB
include hx1

theorem QEC.Coding.ProbabilisticConstruction.avoid_union_lower (T U : Finset I)
    (hc : ∀ A ⊆ U, ∀ i ∈ U, i ∉ A →
      μ.real (B i ∩ avoid B (T ∪ A)) ≤ x i * μ.real (avoid B (T ∪ A))) :
    (∏ i ∈ U, (1 - x i)) * μ.real (avoid B T) ≤ μ.real (avoid B (T ∪ U)) := by sorry
