-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_root_distance
-- name    : QEC.Coding.BDL26DecodingGraph.root_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:37:38.210199+00:00
-- url     : https://prove2.me/theorems/87deb925-dd1a-4f3f-b961-2a7f9432c7fb
-- title:
--   BDL26 Decoding Graph: root distance
-- statement:
--   The root's self-distance is zero despite the absence of edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L488-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L488-L489

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.root_distance : rootLevel.graph.distance () () = (0 : WithTop Nat) := by sorry
