-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_distinctVariableDepth
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_distinctVariableDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:16.623689+00:00
-- url     : https://prove2.me/theorems/34bcec42-406f-48e8-8688-86cf17af5130
-- title:
--   Resampling: history Witness distinct Variable Depth
-- statement:
--   The Resampling construction uses the history Witness distinct Variable Depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L25-L28

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_distinctVariableDepth (root : I) (L : List I) :
    DistinctVariableDepth vars root (historyWitness (supportGraph vars) root L) := by sorry
