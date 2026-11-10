-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_jointObservation
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_jointObservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:35:41.977743+00:00
-- url     : https://prove2.me/theorems/4e4688ff-4017-4a46-80fa-dc55284d03b9
-- title:
--   Variable Relabeling: measurable joint Observation
-- statement:
--   The Variable Relabeling construction uses the measurable joint Observation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L382-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L382-L395

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_jointObservation (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (jointObservation (X := X) U B) := by sorry
