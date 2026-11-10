-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_at_x
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:15:57.919824+00:00
-- url     : https://prove2.me/theorems/1e7cf2ed-c40b-4bc7-8004-1a425f4a3b6d
-- title:
--   BDL26 RXDecoder Adapter: x Extend at x
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Extend at x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L36-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L36-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_x (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (a : DoubleCylinderEdge P x S) :
    xExtend P S x w (Sum.inl ⟨x,a⟩) = w a := by sorry
