-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_counters_conjugacy
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_conjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:33:21.183276+00:00
-- url     : https://prove2.me/theorems/dc81343d-1118-4aca-8227-03e124c6c844
-- title:
--   Variable Relabeling: counters conjugacy
-- statement:
--   All times and every variable, including absorbing clean states.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L165-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L165-L170

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_conjugacy (T : HTable V X) (m : ℕ) :
    counters (codedSupport u U) (codedBad u U B) (encodeTable u T) m=
      encodeAssignment u (counters U B T m) := by sorry
