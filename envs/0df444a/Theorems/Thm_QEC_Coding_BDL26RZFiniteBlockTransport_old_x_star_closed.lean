-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_old_x_star_closed
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.old_x_star_closed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:16:56.135296+00:00
-- url     : https://prove2.me/theorems/9e3a9800-c88c-4821-83c9-f1b302ed4ef7
-- title:
--   BDL26 RZFinite Block Transport: old x star closed
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the old x star closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L960-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L960-L965

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.old_x_star_closed (x : (Old S depth i).X) :
    star S depth i odd (incidentQ S depth i x)
      (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x))=
    inputBlocks S depth i odd (incidentQ S depth i x)
      (Coordinates.neighborZ (Old S depth i) (incidentQ S depth i x)) := by sorry
