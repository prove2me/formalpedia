-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_output_good
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.output_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:28:12.135138+00:00
-- url     : https://prove2.me/theorems/403bc908-dde5-4904-ad81-dc47d9fb20a2
-- title:
--   Resampling: output good
-- statement:
--   The Resampling construction uses the output good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L110-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L110-L112

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.output_good (R : Table (X := X)) (h : Halts vars bad R) :
    ∀ i, output vars bad R ∉ localEvent vars bad i := by sorry
