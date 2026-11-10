-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_localEvent_decode
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.localEvent_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:34:39.976496+00:00
-- url     : https://prove2.me/theorems/e08552dd-9e67-4b46-8ba8-a69a79d89da8
-- title:
--   Variable Relabeling: local Event decode
-- statement:
--   The Variable Relabeling construction uses the local Event decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L77-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L77-L83

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.localEvent_decode (u : A ≃ V) (U : I → Finset V)
    (B : ∀ i, Set (U i → X)) (i : I) (z : A → X) :
    z∈localEvent (codedSupport u U) (codedBad u U B) i ↔
      decodeAssignment u z∈localEvent U B i := by sorry
