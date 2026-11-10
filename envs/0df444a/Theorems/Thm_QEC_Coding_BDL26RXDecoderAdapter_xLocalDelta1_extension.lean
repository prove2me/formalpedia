-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLocalDelta1_extension
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xLocalDelta1_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:51:16.182265+00:00
-- url     : https://prove2.me/theorems/9952ad27-305b-4dc3-ad43-b3802cce5f63
-- title:
--   BDL26 RXDecoder Adapter: x Local Delta1 extension
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Local Delta1 extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L56-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L56-L78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xLocalDelta1_extension (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rxLocalDelta1 P S (xExtend P S x w) =
      xSyndromeExtend P S x (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) w) := by sorry
