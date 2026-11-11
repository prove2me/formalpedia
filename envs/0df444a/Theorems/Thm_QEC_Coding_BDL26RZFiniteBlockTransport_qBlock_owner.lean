-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_qBlock_owner
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.qBlock_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:34:46.242603+00:00
-- url     : https://prove2.me/theorems/08c97e9b-d124-44e1-b5d4-5f6751aff866
-- title:
--   BDL26 RZFinite Block Transport: q Block owner
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the q Block owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L716-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L716-L722

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.qBlock_owner (q : (Old S depth i).Q) (p : FamilyQ S depth i.succ) :
    p ∈ qBlocks S depth i odd {q} ↔
      rzCorrectionOwner (Old S depth i) S (coord1 S depth i odd p)=Vertex.q q := by sorry
