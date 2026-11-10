-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:32:54.356498+00:00
-- url     : https://prove2.me/theorems/b2ec61e3-bb21-4018-9322-05c55be2814a
-- title:
--   Variable Relabeling: decode encode assignment
-- statement:
--   The Variable Relabeling construction uses the decode encode assignment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L58-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L58-L59

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_assignment (u : A ≃ V) (z : V → X) :
    decodeAssignment u (encodeAssignment u z)=z := by sorry
