-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeExtend_outside
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:50:18.921217+00:00
-- url     : https://prove2.me/theorems/5960faf5-7cde-49e8-b739-3bb90801cbe0
-- title:
--   BDL26 RXDecoder Adapter: x Syndrome Extend outside
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Syndrome Extend outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L32-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L32-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_outside (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.x x) : xSyndromeExtend P S x w p = 0 := by sorry
