-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_eventProbability_nonneg
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.eventProbability_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:23:13.368483+00:00
-- url     : https://prove2.me/theorems/f851d928-350c-450c-b614-c086f9f5e984
-- title:
--   Resampling: event Probability nonneg
-- statement:
--   The Resampling construction uses the event Probability nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L67-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean#L67-L68

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

theorem QEC.Coding.ProbabilisticConstruction.Resampling.eventProbability_nonneg (i : I) : 0 ≤ eventProbability vars ν bad i := by sorry
