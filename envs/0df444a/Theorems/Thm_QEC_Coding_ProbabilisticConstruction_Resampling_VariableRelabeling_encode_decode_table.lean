-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_table
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:33:20.234525+00:00
-- url     : https://prove2.me/theorems/f7d27897-4bb4-45c7-83f9-6c91bb6d4a4e
-- title:
--   Variable Relabeling: encode decode table
-- statement:
--   The Variable Relabeling construction uses the encode decode table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L67-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L67-L71

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_table (u : A ≃ V) (T : HTable A X) :
    encodeTable u (decodeTable u T)=T := by sorry
