-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_tannerLevel_isomorphism
-- name    : QEC.Coding.BDL26DecodingGraph.tannerLevel_isomorphism
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:01:29.672764+00:00
-- url     : https://prove2.me/theorems/0a0ae549-0178-4c0b-8374-181ff5f0ef2c
-- title:
--   BDL26 Decoding Graph: tanner Level isomorphism
-- statement:
--   The Tanner equivalence uses the actual presentation's vertex labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L80-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L80-L83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.tannerLevel_isomorphism (P : TannerSquarePresentation) :
    LevelGraphTannerIsomorphism (tannerLevel P) (tannerSkeleton P)
      (vertexKind P) (Equiv.refl (Vertex P)) := by sorry
