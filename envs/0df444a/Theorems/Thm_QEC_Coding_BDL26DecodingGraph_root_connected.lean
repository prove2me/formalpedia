-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_root_connected
-- name    : QEC.Coding.BDL26DecodingGraph.root_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:36:55.750079+00:00
-- url     : https://prove2.me/theorems/1ab73b9f-20ca-44e5-b48d-ffef47ad8e37
-- title:
--   BDL26 Decoding Graph: root connected
-- statement:
--   The BDL26 Decoding Graph construction uses the root connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L356-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L356-L360

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.root_connected (S : OddScale) (depth : Nat) (hdepth : 0 < depth) :
    (decodingGraph S depth).RootConnectedToLevelOne hdepth := by sorry
