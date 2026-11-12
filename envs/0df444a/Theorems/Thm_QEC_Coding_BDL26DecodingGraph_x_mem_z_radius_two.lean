-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_x_mem_z_radius_two
-- name    : QEC.Coding.BDL26DecodingGraph.x_mem_z_radius_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:03:32.257526+00:00
-- url     : https://prove2.me/theorems/f0da9189-4c83-4ba2-a2e5-e0e8b0396c86
-- title:
--   BDL26 Decoding Graph: x mem z radius two
-- statement:
--   The source X-to-Z radius-two formula has precisely the common-Q incidence witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L451-L460
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L451-L460

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.x_mem_z_radius_two (S : OddScale) (n : Nat)
    (x : (state S n).presentation.X) (z : (state S n).presentation.Z) :
    Vertex.x x ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S n).presentation).graph (.z z) 2 ↔
      ∃ q : (state S n).presentation.Q,
        (state S n).presentation.xq x q = true ∧
        (state S n).presentation.qz q z = true := by sorry
