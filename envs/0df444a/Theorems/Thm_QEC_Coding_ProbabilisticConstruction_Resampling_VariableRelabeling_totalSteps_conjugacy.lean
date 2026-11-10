-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_totalSteps_conjugacy
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.totalSteps_conjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:33:52.342239+00:00
-- url     : https://prove2.me/theorems/74cda690-be20-495c-a026-99cb066e700d
-- title:
--   Variable Relabeling: total Steps conjugacy
-- statement:
--   The Variable Relabeling construction uses the total Steps conjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L238-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L238-L240

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.totalSteps_conjugacy (T : HTable V X) :
    totalSteps (codedSupport u U) (codedBad u U B) (encodeTable u T)=totalSteps U B T := by sorry
