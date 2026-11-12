-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_root_neighborhood
-- name    : QEC.Coding.BDL26DecodingGraph.root_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:04:54.152547+00:00
-- url     : https://prove2.me/theorems/455ef162-17b3-48eb-8929-94f54cb1298c
-- title:
--   BDL26 Decoding Graph: root neighborhood
-- statement:
--   Every incoming root neighborhood contains exactly the singleton root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L492-L496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L492-L496

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.root_neighborhood (radius : Nat) :
    LocalRegion.directedNeighborhood rootLevel.graph () radius = {()} := by sorry
