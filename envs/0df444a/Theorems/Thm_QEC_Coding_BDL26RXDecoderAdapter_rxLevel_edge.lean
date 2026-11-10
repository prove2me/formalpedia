-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxLevel_edge
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxLevel_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:27:46.992143+00:00
-- url     : https://prove2.me/theorems/d04e11c9-538b-4892-a8b0-c95ec6b2f75d
-- title:
--   BDL26 RXDecoder Adapter: rx Level edge
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the rx Level edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L35-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L35-L36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.rxLevel_edge (P : TannerSquarePresentation) (u v) :
    (rxLevel P).graph.edge u v = (tannerLevel P).graph.edge (vertexEquiv P u) (vertexEquiv P v) := by sorry
