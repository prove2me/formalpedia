-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_reachable_two
-- name    : QEC.Coding.BDL26DecodingGraph.reachable_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:36:57.082924+00:00
-- url     : https://prove2.me/theorems/6ed72ff4-d1d7-4cf5-8611-932bf3534ceb
-- title:
--   BDL26 Decoding Graph: reachable two
-- statement:
--   Two directed steps retain the centre, incoming neighbors, and two-edge predecessors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L376-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L376-L382

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.reachable_two (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.reachableWithin 2 u v = true ↔
      u = v ∨ tannerDirected P u v = true ∨
        ∃ w : Vertex P, tannerDirected P u w = true ∧ tannerDirected P w v = true := by sorry
