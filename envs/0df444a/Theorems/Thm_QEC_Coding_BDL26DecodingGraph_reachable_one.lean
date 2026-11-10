-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_reachable_one
-- name    : QEC.Coding.BDL26DecodingGraph.reachable_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:11:09.118128+00:00
-- url     : https://prove2.me/theorems/96729c97-b84f-4175-b77c-daf1bdca1b39
-- title:
--   BDL26 Decoding Graph: reachable one
-- statement:
--   Expanding one directed step retains the centre and its incoming neighbors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L370-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L370-L373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.reachable_one (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.reachableWithin 1 u v = true ↔
      u = v ∨ tannerDirected P u v = true := by sorry
