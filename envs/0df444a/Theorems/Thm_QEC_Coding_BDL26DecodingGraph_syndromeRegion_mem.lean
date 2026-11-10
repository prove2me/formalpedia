-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
-- name    : QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:09:41.010528+00:00
-- url     : https://prove2.me/theorems/d084b28e-41c3-4eed-a502-c7ef7e001c5a
-- title:
--   BDL26 Decoding Graph: syndrome Region mem
-- statement:
--   The BDL26 Decoding Graph construction uses the syndrome Region mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L478-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L478-L485

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (syndromeRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true ∨
        ∃ w : Vertex (state S n).presentation,
          tannerDirected (state S n).presentation u w = true ∧
          tannerDirected (state S n).presentation w v = true := by sorry
