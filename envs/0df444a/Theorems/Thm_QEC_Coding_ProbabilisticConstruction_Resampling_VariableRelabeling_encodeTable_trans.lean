-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encodeTable_trans
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encodeTable_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:24.871251+00:00
-- url     : https://prove2.me/theorems/f17cee8b-5883-4c62-b7e6-de2dfd945002
-- title:
--   Variable Relabeling: encode Table trans
-- statement:
--   The Variable Relabeling construction uses the encode Table trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L258-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L258-L259

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encodeTable_trans (v : D ≃ A) (T : HTable V X) :
    encodeTable (v.trans u) T=encodeTable v (encodeTable u T) := by sorry
