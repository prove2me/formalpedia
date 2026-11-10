-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_q
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:15:57.649543+00:00
-- url     : https://prove2.me/theorems/568a332d-f7e7-4d31-9218-dbd65951cc2a
-- title:
--   BDL26 RXDecoder Adapter: q Flow at q
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Flow at q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L156-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L156-L159

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_q (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (e : QDoubleCylinderEdge P r S) :
    qFlow P S q w (Sum.inl (Sum.inr ⟨r,e⟩)) = 0 := by sorry
