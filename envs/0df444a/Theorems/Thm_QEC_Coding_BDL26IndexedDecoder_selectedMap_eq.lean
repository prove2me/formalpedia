-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
-- name    : QEC.Coding.BDL26IndexedDecoder.selectedMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:52:18.841655+00:00
-- url     : https://prove2.me/theorems/9869e16d-0c70-4060-9104-680dac25f17c
-- title:
--   BDL26 Indexed Decoder: selected Map eq
-- statement:
--   The BDL26 Indexed Decoder construction uses the selected Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L73-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L73-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical
universe u

theorem QEC.Coding.BDL26IndexedDecoder.selectedMap_eq (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    (indexedDecoderData S depth).selectedMap i = indexedEdgeMap S depth i := by sorry
