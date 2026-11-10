-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
-- name    : QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:08:54.400529+00:00
-- url     : https://prove2.me/theorems/da528fdf-c174-4051-ac5b-5fecd667dae8
-- title:
--   BDL26 Decoding Graph: correction Region mem
-- statement:
--   The BDL26 Decoding Graph construction uses the correction Region mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L472-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L472-L476

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.correctionRegion_mem (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (correctionRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true := by sorry
