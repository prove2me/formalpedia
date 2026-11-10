-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_weight
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qFlow_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:26:20.869252+00:00
-- url     : https://prove2.me/theorems/4b1656cd-ef5a-424d-8708-f054ff0d9203
-- title:
--   BDL26 RXDecoder Adapter: q Flow weight
-- statement:
--   Count both actual copies of every Z label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L179-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L179-L185

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qFlow_weight (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    HammingWeight (qFlow P S q w) = ∑ z : P.Z, HammingWeight (rxQOutgoing P q S w z) := by sorry
