-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_avoid
-- name    : QEC.Coding.ProbabilisticConstruction.measurableSet_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:10.860701+00:00
-- url     : https://prove2.me/theorems/803aeaaf-07de-49a4-98b9-b9ff86a28b5a
-- title:
--   Probabilistic Construction: measurable Set avoid
-- statement:
--   The Probabilistic Construction construction uses the measurable Set avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L48-L52

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

theorem QEC.Coding.ProbabilisticConstruction.measurableSet_avoid (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (S : Finset I) : MeasurableSet (avoid B S) := by sorry
