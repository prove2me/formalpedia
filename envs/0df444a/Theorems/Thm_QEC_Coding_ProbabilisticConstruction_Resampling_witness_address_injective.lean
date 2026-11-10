-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witness_address_injective
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.witness_address_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:22.488206+00:00
-- url     : https://prove2.me/theorems/3ea3dc7a-f61f-47fa-9f16-1119024bc0f0
-- title:
--   Resampling: witness address injective
-- statement:
--   Variable ranks assign genuinely distinct table addresses to all node-variable slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L66-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L66-L84

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)

theorem QEC.Coding.ProbabilisticConstruction.Resampling.witness_address_injective (root : I) (P : Finset (List I))
    (hd : DistinctVariableDepth vars root P) :
    Function.Injective (fun s : (p : P) × vars (pathLabel root p.val) =>
      (s.2.val, variableRank vars root P s.1.val s.2.val)) := by sorry
