-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_topOutput_eq
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.topOutput_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:40:54.556856+00:00
-- url     : https://prove2.me/theorems/edcf6fcb-70e5-4884-92b0-90580ccaffb0
-- title:
--   BDL26 RZFinite Block Transport: top Output eq
-- statement:
--   The BDL26 RZFinite Block Transport construction uses the top Output eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L998-L1002
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L998-L1002

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
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks

theorem QEC.Coding.BDL26RZFiniteBlockTransport.topOutput_eq (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    topOutput S j a=run S (2*j+4) (topStep j) (topStep_odd j) a := by sorry
