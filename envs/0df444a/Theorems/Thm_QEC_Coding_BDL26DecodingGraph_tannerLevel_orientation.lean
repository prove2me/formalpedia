-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_tannerLevel_orientation
-- name    : QEC.Coding.BDL26DecodingGraph.tannerLevel_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:01:49.332886+00:00
-- url     : https://prove2.me/theorems/5a5d412c-cf36-4f76-b58e-06f78959e32b
-- title:
--   BDL26 Decoding Graph: tanner Level orientation
-- statement:
--   The BDL26 Decoding Graph construction uses the tanner Level orientation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L75-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L75-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.tannerLevel_orientation (P : TannerSquarePresentation) :
    LevelGraphDirectedOrientation (tannerLevel P) := by sorry
