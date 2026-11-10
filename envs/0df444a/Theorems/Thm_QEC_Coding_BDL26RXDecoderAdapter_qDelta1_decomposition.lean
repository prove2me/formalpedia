-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qDelta1_decomposition
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qDelta1_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:52:01.375451+00:00
-- url     : https://prove2.me/theorems/e1737bd4-eb7c-40a2-b23a-9b6ca7879bca
-- title:
--   BDL26 RXDecoder Adapter: q Delta1 decomposition
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Delta1 decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L114-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L114-L122

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    rxCoboundary1 P S (qExtend P S q w) =
      qSyndromeExtend P S q (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) w) +
        qFlow P S q w := by sorry
