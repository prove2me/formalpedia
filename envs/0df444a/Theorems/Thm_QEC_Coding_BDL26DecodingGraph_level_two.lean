-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_level_two
-- name    : QEC.Coding.BDL26DecodingGraph.level_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:02:40.424688+00:00
-- url     : https://prove2.me/theorems/0e1a4d31-74ee-4379-b1cd-51babe9d440c
-- title:
--   BDL26 Decoding Graph: level two
-- statement:
--   Level two is Tanner presentation one, the actual RX successor of the seed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L363-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L363-L365

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.level_two (S : OddScale) :
    level S 2 = tannerLevel (rxState S baseState).presentation := by sorry
