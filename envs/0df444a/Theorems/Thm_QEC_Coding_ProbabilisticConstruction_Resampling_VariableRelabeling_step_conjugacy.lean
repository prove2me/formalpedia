-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_step_conjugacy
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.step_conjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:34:43.137337+00:00
-- url     : https://prove2.me/theorems/78dd799b-a3d2-4b0b-9cd2-7971534c0805
-- title:
--   Variable Relabeling: step conjugacy
-- statement:
--   The Variable Relabeling construction uses the step conjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L123-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L123-L162

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.step_conjugacy (T : HTable V X) (c : Counters V) :
    step (codedSupport u U) (codedBad u U B) (encodeTable u T) (encodeAssignment u c)=
      encodeAssignment u (step U B T c) := by sorry
