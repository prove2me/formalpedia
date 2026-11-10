-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_compatible
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:25:46.809198+00:00
-- url     : https://prove2.me/theorems/bf04de2b-0c3f-4e29-b91a-1d226d15b295
-- title:
--   Resampling: occurrence Tree compatible
-- statement:
--   The Resampling construction uses the occurrence Tree compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L91-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L91-L96

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_compatible (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) :
    R ∈ compatible vars bad i
      (witnessPaths (supportGraph vars) (T + 1) i (occurrenceTree vars bad R T i n)) := by sorry
