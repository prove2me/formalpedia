-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_decoder_owner_q
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.decoder_owner_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:16:02.432562+00:00
-- url     : https://prove2.me/theorems/f664a46d-92b6-4ad3-8b23-99dbc46d8af3
-- title:
--   BDL26 RZFinite Block Transport: decoder owner q
-- statement:
--   Physical Q blocks stay outside the ORIGINAL decoder correction owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L729-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L729-L738

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.decoder_owner_q (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (rzData S depth i odd).correctionOwner ((coord1 S depth i odd).symm (.inr ⟨q,v⟩))=none := by sorry
