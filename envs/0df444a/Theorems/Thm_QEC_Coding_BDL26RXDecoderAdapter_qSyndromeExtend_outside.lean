-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeExtend_outside
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:50:29.810404+00:00
-- url     : https://prove2.me/theorems/b94d9325-7691-4cc7-977e-18df84c55ad5
-- title:
--   BDL26 RXDecoder Adapter: q Syndrome Extend outside
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Syndrome Extend outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L40-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L40-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_outside (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (p : RX2 P S)
    (hp : rxSyndromeOwner P S p ≠ Vertex.q q) : qSyndromeExtend P S q w p = 0 := by sorry
