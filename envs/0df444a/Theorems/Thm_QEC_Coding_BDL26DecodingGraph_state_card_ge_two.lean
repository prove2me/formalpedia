-- Prove2me | Theorems.Thm_QEC_Coding_BDL26DecodingGraph_state_card_ge_two
-- name    : QEC.Coding.BDL26DecodingGraph.state_card_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:10:27.614056+00:00
-- url     : https://prove2.me/theorems/d268f985-7822-4494-b13a-52344213497d
-- title:
--   BDL26 Decoding Graph: state card ge two
-- statement:
--   The BDL26 Decoding Graph construction uses the state card ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L406-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean#L406-L409

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder

theorem QEC.Coding.BDL26DecodingGraph.state_card_ge_two (S : OddScale) (n : Nat) :
    2 ≤ Fintype.card (Vertex (state S n).presentation) := by sorry
