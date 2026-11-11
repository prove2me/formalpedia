-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_zBlock_eq_correctionRegion
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.zBlock_eq_correctionRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:19:54.939257+00:00
-- url     : https://prove2.me/theorems/29c3160e-b5f0-4c42-bd76-eafbfd69e950
-- title:
--   BDL26 RZFinite Block Transport: z Block eq correction Region
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the z Block eq correction Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L491-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L491-L501

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.zBlock_eq_correctionRegion (z : (Old S depth i).Z) :
    zBlocks S depth i odd {z}=(rzData S depth i odd).correctionRegion z := by sorry
