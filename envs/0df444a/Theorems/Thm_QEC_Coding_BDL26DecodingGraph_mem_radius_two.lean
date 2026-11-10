-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_mem_radius_two
-- name    : QEC.Coding.BDL26DecodingGraph.mem_radius_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:13.065494+00:00
-- url     : https://prove2.me/theorems/68d029b9-c8d2-4cdf-92a7-868f3697d917
-- title:
--   BDL26 Decoding Graph: mem radius two
-- statement:
--   The exact raw coarse-syndrome radius-two carrier, with directed incoming paths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L424-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L424-L434

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.mem_radius_two (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ LocalRegion.directedNeighborhood (tannerLevel (state S n).presentation).graph v 2 ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true ∨
        ∃ w : Vertex (state S n).presentation,
          tannerDirected (state S n).presentation u w = true ∧
          tannerDirected (state S n).presentation w v = true := by sorry
