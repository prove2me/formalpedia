-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encodeAssignment_trans
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encodeAssignment_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:20.468925+00:00
-- url     : https://prove2.me/theorems/60fabff5-9fdd-4f5d-95ee-bfc92b153cd2
-- title:
--   Variable Relabeling: encode Assignment trans
-- statement:
--   The Variable Relabeling construction uses the encode Assignment trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L261-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L261-L262

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
variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encodeAssignment_trans (v : D ≃ A) (z : V → X) :
    encodeAssignment (v.trans u) z=encodeAssignment v (encodeAssignment u z) := by sorry
