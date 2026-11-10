-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_at_q
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:13:56.914441+00:00
-- url     : https://prove2.me/theorems/fda1ed2f-de1a-4852-9518-581288664f7b
-- title:
--   BDL26 RXDecoder Adapter: x Extend at q
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Extend at q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L46-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L46-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_q (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (q : P.Q)
    (v : QDoubleCylinderVertex P q S) : xExtend P S x w (Sum.inr ⟨q,v⟩) = 0 := by sorry
