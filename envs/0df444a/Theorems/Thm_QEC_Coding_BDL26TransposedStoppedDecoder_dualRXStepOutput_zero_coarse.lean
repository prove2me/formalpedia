-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRXStepOutput_zero_coarse
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_zero_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:33:50.571656+00:00
-- url     : https://prove2.me/theorems/713cf377-b3b3-4e95-87c8-d0b710cf2fc3
-- title:
--   BDL26 Transposed Stopped Decoder: dual RXStep Output zero coarse
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual RXStep Output zero coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L679-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L679-L691

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_zero_coarse (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRXStepOutput S depth i h sigma).coarse.val = 0 := by sorry
