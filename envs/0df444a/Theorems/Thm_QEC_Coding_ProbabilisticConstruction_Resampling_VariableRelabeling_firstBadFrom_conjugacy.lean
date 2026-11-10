-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_firstBadFrom_conjugacy
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.firstBadFrom_conjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:34:34.825204+00:00
-- url     : https://prove2.me/theorems/265dca24-2f5a-4485-883d-808df3701397
-- title:
--   Variable Relabeling: first Bad From conjugacy
-- statement:
--   Every original list, including empty/repeated/non-sorted lists, is retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L89-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean#L89-L100

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.firstBadFrom_conjugacy (L : List I) (z : A → X) :
    firstBadFrom (localEvent (codedSupport u U) (codedBad u U B)) L z=
      firstBadFrom (localEvent U B) L (decodeAssignment u z) := by sorry
