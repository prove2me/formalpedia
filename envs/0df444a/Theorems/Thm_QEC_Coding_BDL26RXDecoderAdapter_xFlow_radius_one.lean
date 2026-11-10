-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_radius_one
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xFlow_radius_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:55:33.021658+00:00
-- url     : https://prove2.me/theorems/8bb8d56e-5240-4d8e-b678-b58828ceb504
-- title:
--   BDL26 RXDecoder Adapter: x Flow radius one
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Flow radius one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L76-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean#L76-L90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xFlow_radius_one (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (p : RX2 P S) (hp : xFlow P S x w p ≠ 0) :
    DirectedGraph.distance (rxLevel P).graph (Sum.inl x) (topCenter P S p) ≤ 1 := by sorry
