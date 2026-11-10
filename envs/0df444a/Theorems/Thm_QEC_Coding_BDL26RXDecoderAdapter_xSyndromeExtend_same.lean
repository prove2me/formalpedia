-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeExtend_same
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:49:27.414324+00:00
-- url     : https://prove2.me/theorems/67807540-b68e-4171-9123-fa4ea6049cf8
-- title:
--   BDL26 RXDecoder Adapter: x Syndrome Extend same
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Syndrome Extend same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L22-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L22-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xSyndromeExtend_same (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderFace P x S)) (f : DoubleCylinderFace P x S) :
    xSyndromeExtend P S x w (Sum.inl (Sum.inl ⟨x,f⟩)) = w f := by sorry
