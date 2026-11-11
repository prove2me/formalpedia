-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_stepPropagation_mono
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.stepPropagation_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:49:56.089992+00:00
-- url     : https://prove2.me/theorems/53fb34d6-f6e9-4635-8f2c-9e003becd211
-- title:
--   BDL26 History Syndrome Sensitivity: step Propagation mono
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the step Propagation mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L144-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L144-L153

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.stepPropagation_mono
    {A B : Finset (FamilyZ S depth i.succ)} (hab : A ⊆ B) :
    stepPropagation S depth i A ⊆ stepPropagation S depth i B := by sorry
