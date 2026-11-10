-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta0_apply
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_delta0_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:15:23.380252+00:00
-- url     : https://prove2.me/theorems/912422e9-5b22-44c4-8678-3bf0b8bbbe73
-- title:
--   BDL26 RXDecoder Adapter: local Cx delta0 apply
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx delta0 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L54-L60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_delta0_apply (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S)) (e : DoubleCylinderEdge P x S) :
    wordLinearMapTranspose (localCx P S x).boundary1 w (xCorrectionEquiv P S x e) =
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S) w e := by sorry
