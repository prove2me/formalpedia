-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_tanner_two_edge_xz
-- name    : QEC.Coding.BDL26DecodingGraph.tanner_two_edge_xz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:37:19.490241+00:00
-- url     : https://prove2.me/theorems/406b8248-bd4e-4313-ae2e-0c776b90d740
-- title:
--   BDL26 Decoding Graph: tanner two edge xz
-- statement:
--   A two-edge directed predecessor of Z must be X through an actual Q neighbor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L437-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L437-L448

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.tanner_two_edge_xz (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    (∃ w : Vertex P,
      tannerDirected P (.x x) w = true ∧ tannerDirected P w (.z z) = true) ↔
      ∃ q : P.Q, P.xq x q = true ∧ P.qz q z = true := by sorry
