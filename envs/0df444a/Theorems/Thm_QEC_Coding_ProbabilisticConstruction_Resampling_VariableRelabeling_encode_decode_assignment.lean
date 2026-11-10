-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_assignment
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:33:00.156013+00:00
-- url     : https://prove2.me/theorems/805ea620-683c-434e-9440-91f6815d85f5
-- title:
--   Variable Relabeling: encode decode assignment
-- statement:
--   The Variable Relabeling construction uses the encode decode assignment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L60-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L60-L61

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_assignment (u : A ≃ V) (z : A → X) :
    encodeAssignment u (decodeAssignment u z)=z := by sorry
