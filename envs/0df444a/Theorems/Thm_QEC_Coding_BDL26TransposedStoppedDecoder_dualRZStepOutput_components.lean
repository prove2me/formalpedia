-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRZStepOutput_components
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualRZStepOutput_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:35:49.961829+00:00
-- url     : https://prove2.me/theorems/c62771bb-42a3-4746-9cb4-092c8a262ced
-- title:
--   BDL26 Transposed Stopped Decoder: dual RZStep Output components
-- statement:
--   Exact original component order, including duplicate or zero entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L640-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L640-L646

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualRZStepOutput_components (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRZStepOutput S depth i h sigma).localComponents =
      (BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S (dualRZMaterializedInput S depth i h sigma)).localComponents.map
        (wordEquiv (dualRZTopQ S depth i h)) := by sorry
