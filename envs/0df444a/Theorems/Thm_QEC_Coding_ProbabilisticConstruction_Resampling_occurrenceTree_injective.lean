-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceTree_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:25:47.423673+00:00
-- url     : https://prove2.me/theorems/cc0f1b06-d29c-444f-8be7-3f65ff8fe3c2
-- title:
--   Resampling: occurrence Tree injective
-- statement:
--   Different occurrences of an event produce different proper witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L99-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean#L99-L115

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceTree_injective (R : Table (X := X)) (T : ℕ) (i : I) :
    Function.Injective (occurrenceTree vars bad R T i) := by sorry
