-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:55:09.594391+00:00
-- url     : https://prove2.me/theorems/ad3b0d4f-6f06-4ced-b0fe-e905ae9c2134
-- title:
--   BDL26 RXDecoder Adapter: x Syndrome Equiv val
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Syndrome Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L132-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L132-L134

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (f : DoubleCylinderFace P x S) :
    (xSyndromeEquiv P S x f).1 = Sum.inl (Sum.inl ⟨x,f⟩) := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
