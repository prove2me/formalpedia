-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_jointObservation_law
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:11.928434+00:00
-- url     : https://prove2.me/theorems/ea9cb95a-69dc-4467-9f61-7bce14aaafbd
-- title:
--   Variable Relabeling: joint Observation law
-- statement:
--   Full joint law is DERIVED from coordinate reindexing, never a marginal assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L405-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L405-L414

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation_law (hB : ∀ i, MeasurableSet (B i))
    (ν : V → Measure X) [∀ v, IsProbabilityMeasure (ν v)] :
    (tableLaw (fun a => ν (u a))).map (decodedObservation u U B)=
      (tableLaw ν).map (jointObservation U B) := by sorry
