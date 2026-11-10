-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decodedObservation_eq
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decodedObservation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:35:19.259257+00:00
-- url     : https://prove2.me/theorems/01848f7f-d4a9-4f9b-bfa4-45e3eaae2175
-- title:
--   Variable Relabeling: decoded Observation eq
-- statement:
--   The Variable Relabeling construction uses the decoded Observation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L356-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L356-L359

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
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decodedObservation_eq (T : HTable A X) :
    decodedObservation u U B T=jointObservation U B (decodeTable u T) := by sorry
