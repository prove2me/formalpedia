-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_indexedFamily_levelTwo
-- name    : QEC.Coding.BDL26IndexedDecoder.indexedFamily_levelTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:31:19.548867+00:00
-- url     : https://prove2.me/theorems/dd0b2a25-f66b-489d-a4e3-2b8d0e198f9a
-- title:
--   BDL26 Indexed Decoder: indexed Family level Two
-- statement:
--   The two-level specialization uses identical carriers and differentials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L79-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/IndexedDecoder.lean#L79-L80

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

theorem QEC.Coding.BDL26IndexedDecoder.indexedFamily_levelTwo (S : OddScale) :
    indexedFamily S 2 = BDL26LevelTwoDecoder.decoderFamily S := by sorry
