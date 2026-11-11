-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_stepPropagation_card
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.stepPropagation_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:48:02.189649+00:00
-- url     : https://prove2.me/theorems/84b828e6-1d94-470d-8d0f-759381ae38fb
-- title:
--   BDL26 History Syndrome Sensitivity: step Propagation card
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the step Propagation card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L155-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L155-L161

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.stepPropagation_card (A : Finset (FamilyZ S depth i.succ)) :
    (stepPropagation S depth i A).card ≤ stepFactor depth i * A.card := by sorry
