-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xDelta1_decomposition
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xDelta1_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:27:32.905212+00:00
-- url     : https://prove2.me/theorems/e9714f4c-a6ea-488c-b58c-b5be005bcc3f
-- title:
--   BDL26 RXDecoder Adapter: x Delta1 decomposition
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Delta1 decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L104-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L104-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) :
    rxCoboundary1 P S (xExtend P S x w) =
      xSyndromeExtend P S x (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) w) +
        xFlow P S x w := by sorry
