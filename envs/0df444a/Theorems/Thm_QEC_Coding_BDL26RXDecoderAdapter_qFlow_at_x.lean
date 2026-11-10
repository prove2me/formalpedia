-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_x
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:15:32.411915+00:00
-- url     : https://prove2.me/theorems/bb2f3f0e-2afd-4663-af43-8a55ca375c6d
-- title:
--   BDL26 RXDecoder Adapter: q Flow at x
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Flow at x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L148-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L148-L154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_x (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (x : P.X)
    (f : DoubleCylinderFace P x S) : qFlow P S q w (Sum.inl (Sum.inl ⟨x,f⟩)) = 0 := by sorry
