-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_coordinates
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:22:07.838279+00:00
-- url     : https://prove2.me/theorems/cb513fa2-303b-4758-b727-90b973830d9c
-- title:
--   BDL26 RZFinite Block Transport: lower Error coordinates
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the lower Error coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L506-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L506-L508

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_coordinates (a b : Upper S depth i) :
    lowerError S depth i odd a b=rzQParity (Old S depth i) S (read1 S depth i odd (a+b)) := by sorry
