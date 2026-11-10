-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qExtend_at_x
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qExtend_at_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:21:37.322498+00:00
-- url     : https://prove2.me/theorems/9fe9ff31-fad4-48f4-854c-8cdd77633890
-- title:
--   BDL26 RXDecoder Adapter: q Extend at x
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Extend at x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L55-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L55-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qExtend_at_x (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X)
    (e : DoubleCylinderEdge P x S) : qExtend P S q w (Sum.inl ⟨x,e⟩) = 0 := by sorry
