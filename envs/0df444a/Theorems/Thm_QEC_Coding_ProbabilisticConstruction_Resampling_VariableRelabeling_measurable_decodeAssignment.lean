-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeAssignment
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_decodeAssignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:37:16.739237+00:00
-- url     : https://prove2.me/theorems/e9dedf91-12df-49a9-a851-ca7196e7d4c9
-- title:
--   Variable Relabeling: measurable decode Assignment
-- statement:
--   The Variable Relabeling construction uses the measurable decode Assignment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L281-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L281-L282

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_decodeAssignment : Measurable (decodeAssignment (X := X) u) := by sorry
