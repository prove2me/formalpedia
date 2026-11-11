-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_footprint_localized
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.footprint_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:35:37.525311+00:00
-- url     : https://prove2.me/theorems/d5d33133-02e1-431d-9e0f-35a22b0565ed
-- title:
--   BDL26 RZFinite Block Transport: footprint localized
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the footprint localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L883-L897
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L883-L897

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.footprint_localized (a b : Upper S depth i) :
    hammingSupport (a+b) ⊆ inputBlocks S depth i odd
      (footprintQ S depth i odd a b) (footprintZ S depth i odd a b) := by sorry
