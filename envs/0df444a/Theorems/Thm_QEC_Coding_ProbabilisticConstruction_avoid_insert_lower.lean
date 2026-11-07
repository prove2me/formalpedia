-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert_lower
-- name    : QEC.Coding.ProbabilisticConstruction.avoid_insert_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:29.431174+00:00
-- url     : https://prove2.me/theorems/bbfa7aeb-ce59-4bae-ba0c-32630750defa
-- title:
--   Probabilistic Construction: avoid insert lower
-- statement:
--   Insert one avoided event using a cross-multiplied conditional bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L90-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L90-L95

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

theorem QEC.Coding.ProbabilisticConstruction.avoid_insert_lower (i : I) (S : Finset I)
    (hc : μ.real (B i ∩ avoid B S) ≤ x i * μ.real (avoid B S)) :
    (1 - x i) * μ.real (avoid B S) ≤ μ.real (avoid B (insert i S)) := by sorry
