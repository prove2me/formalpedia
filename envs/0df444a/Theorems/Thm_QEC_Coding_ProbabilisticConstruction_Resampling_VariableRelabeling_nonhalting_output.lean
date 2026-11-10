-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_nonhalting_output
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.nonhalting_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:02.825889+00:00
-- url     : https://prove2.me/theorems/85616fbf-51f0-40f3-a25b-081c057f32ea
-- title:
--   Variable Relabeling: nonhalting output
-- statement:
--   Nonhalting returns the initial assignment at unchanged column0, not zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L219-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L219-L228

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.nonhalting_output (T : HTable V X) (h : ¬Halts U B T) :
    output (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      fun a => T (u a,0) := by sorry
