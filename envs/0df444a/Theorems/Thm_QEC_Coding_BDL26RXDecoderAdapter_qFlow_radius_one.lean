-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_radius_one
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qFlow_radius_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:55:34.07874+00:00
-- url     : https://prove2.me/theorems/792db8d3-cb4f-4877-8e6d-5f86580c543c
-- title:
--   BDL26 RXDecoder Adapter: q Flow radius one
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Flow radius one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L92-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L92-L106

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qFlow_radius_one (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (p : RX2 P S) (hp : qFlow P S q w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inr (Sum.inl q)) (topCenter P S p) ≤ 1 := by sorry
