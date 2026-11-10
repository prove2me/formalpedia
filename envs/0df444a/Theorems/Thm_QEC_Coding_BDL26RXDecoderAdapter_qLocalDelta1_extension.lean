-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qLocalDelta1_extension
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qLocalDelta1_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:51:29.965424+00:00
-- url     : https://prove2.me/theorems/baccfaa5-e8f6-429d-b53f-f6f6b404927a
-- title:
--   BDL26 RXDecoder Adapter: q Local Delta1 extension
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Local Delta1 extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L80-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L80-L102

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qLocalDelta1_extension (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxLocalDelta1 P S (qExtend P S q w) =
      qSyndromeExtend P S q (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) := by sorry
