-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_nat_prefixCount
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_nat_prefixCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:35:37.503679+00:00
-- url     : https://prove2.me/theorems/a121a743-ceb0-4617-942f-4e632b0831b5
-- title:
--   Variable Relabeling: measurable nat prefix Count
-- statement:
--   The Variable Relabeling construction uses the measurable nat prefix Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L361-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L361-L380

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_nat_prefixCount (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) (i : I) :
    Measurable (fun T : HTable V X => prefixCount U B T m i) := by sorry
