-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_tannerLevel_coherence
-- name    : QEC.Coding.BDL26DecodingGraph.tannerLevel_coherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:02:16.004763+00:00
-- url     : https://prove2.me/theorems/ed00e9fa-64a0-4b3c-82b1-9bf15ea5bd4f
-- title:
--   BDL26 Decoding Graph: tanner Level coherence
-- statement:
--   The BDL26 Decoding Graph construction uses the tanner Level coherence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L68-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.tannerLevel_coherence (P : TannerSquarePresentation) :
    LevelGraphSkeletonCoherence (tannerLevel P) := by sorry
