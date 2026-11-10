-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_counters_trans
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:54.169167+00:00
-- url     : https://prove2.me/theorems/2d139ce5-c028-4cca-9604-6c71ea34ee2a
-- title:
--   Variable Relabeling: counters trans
-- statement:
--   The Variable Relabeling construction uses the counters trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L264-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L264-L268

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_trans [Fintype D] [DecidableEq D] (v : D ≃ A) (T : HTable V X) (m : ℕ) :
    counters (codedSupport (v.trans u) U) (codedBad (v.trans u) U B)
      (encodeTable v (encodeTable u T)) m=
      encodeAssignment v (encodeAssignment u (counters U B T m)) := by sorry
