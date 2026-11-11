-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRZStepOutput_zero_coarse
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualRZStepOutput_zero_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:33:33.216221+00:00
-- url     : https://prove2.me/theorems/5526d433-f767-40a9-b3f6-8a185ecb445a
-- title:
--   BDL26 Transposed Stopped Decoder: dual RZStep Output zero coarse
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual RZStep Output zero coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L693-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/LocalSteps.lean#L693-L707

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualRZStepOutput_zero_coarse (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRZStepOutput S depth i h sigma).coarse.val = 0 := by sorry
