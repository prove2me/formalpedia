-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_weight
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xFlow_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:48:23.027517+00:00
-- url     : https://prove2.me/theorems/9c9b047c-8591-45c7-a2ad-97607b48f329
-- title:
--   BDL26 RXDecoder Adapter: x Flow weight
-- statement:
--   Count actual tagged coordinates, retaining every adjacent Q label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L162-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L162-L176

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xFlow_weight (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    HammingWeight (xFlow P S x w) =
      ∑ q : P.Q, if h : P.xq x q = true then
        HammingWeight (rxXQDegreeOne P A q x h S w) else 0 := by sorry
