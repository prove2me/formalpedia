-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRXStepOutput_components
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:34:02.837307+00:00
-- url     : https://prove2.me/theorems/18350011-3c98-48b6-8282-9c8c8787f97f
-- title:
--   BDL26 Transposed Stopped Decoder: dual RXStep Output components
-- statement:
--   Exact original component order, including duplicate or zero entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L503-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L503-L508

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26RXDecoderAdapter
open MultiscaleDecoder Coordinates
open scoped Classical BigOperators

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_components (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRXStepOutput S depth i h sigma).localComponents =
      (BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (dualRXMaterializedInput S depth i h sigma)).localComponents.map
        (wordEquiv (dualRXTopQ S depth i h)) := by sorry
