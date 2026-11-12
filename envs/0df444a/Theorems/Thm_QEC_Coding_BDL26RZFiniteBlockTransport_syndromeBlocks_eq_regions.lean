-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_syndromeBlocks_eq_regions
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.syndromeBlocks_eq_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:52:35.591127+00:00
-- url     : https://prove2.me/theorems/f348d09e-ca07-4af5-b8f1-7482422a0e91
-- title:
--   BDL26 RZFinite Block Transport: syndrome Blocks eq regions
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the syndrome Blocks eq regions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L705-L714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L705-L714

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.syndromeBlocks_eq_regions (Z0 : Finset (Old S depth i).Z) :
    syndromeBlocks S depth i odd Z0=Z0.biUnion ((rzData S depth i odd).coarseRegion) := by sorry
