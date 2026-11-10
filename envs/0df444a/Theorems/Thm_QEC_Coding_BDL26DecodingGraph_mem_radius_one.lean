-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_mem_radius_one
-- name    : QEC.Coding.BDL26DecodingGraph.mem_radius_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:37:24.600066+00:00
-- url     : https://prove2.me/theorems/b4e95e0a-fc76-493e-8a74-d611bca3771e
-- title:
--   BDL26 Decoding Graph: mem radius one
-- statement:
--   The graph radius-one carrier used by the raw correction-region interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L412-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L412-L421

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.mem_radius_one (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ LocalRegion.directedNeighborhood (tannerLevel (state S n).presentation).graph v 1 ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true := by sorry
