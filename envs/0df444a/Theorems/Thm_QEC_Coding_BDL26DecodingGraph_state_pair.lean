-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_state_pair
-- name    : QEC.Coding.BDL26DecodingGraph.state_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:37:12.923065+00:00
-- url     : https://prove2.me/theorems/0cae16a6-b807-4a47-b2b7-b64ed35376b2
-- title:
--   BDL26 Decoding Graph: state pair
-- statement:
--   Every constructed presentation has at least two distinct X vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L385-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L385-L404

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.state_pair (S : OddScale) (n : Nat) :
    Nonempty (Fin 2 ↪ Vertex (state S n).presentation) := by sorry
