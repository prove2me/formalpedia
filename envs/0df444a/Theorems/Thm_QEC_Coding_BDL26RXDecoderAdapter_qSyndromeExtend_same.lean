-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeExtend_same
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:49:21.392704+00:00
-- url     : https://prove2.me/theorems/2b7d297d-e34c-44e7-94f7-973674a0b049
-- title:
--   BDL26 RXDecoder Adapter: q Syndrome Extend same
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Syndrome Extend same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L27-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L27-L30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qSyndromeExtend_same (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderEdge P q S)) (e : QDoubleCylinderEdge P q S) :
    qSyndromeExtend P S q w (Sum.inl (Sum.inr ⟨q,e⟩)) = w e := by sorry
