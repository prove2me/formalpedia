-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_restriction_decode
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.restriction_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:34:32.676501+00:00
-- url     : https://prove2.me/theorems/a9b2e086-4248-4e1c-afa0-ac4c1dcf302a
-- title:
--   Variable Relabeling: restriction decode
-- statement:
--   The Variable Relabeling construction uses the restriction decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L73-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L73-L75

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.restriction_decode (u : A ≃ V) (U : I → Finset V) (i : I) (z : A → X) :
    decodeLocal u U i ((codedSupport u U i).restrict z)=
      (U i).restrict (decodeAssignment u z) := by sorry
