-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:53:11.311191+00:00
-- url     : https://prove2.me/theorems/3122197a-b8f6-40bc-abeb-935ad6a5c131
-- title:
--   BDL26 RXDecoder Adapter: q Correction Equiv val
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Correction Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L136-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L136-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (v : QDoubleCylinderVertex P q S) :
    (qCorrectionEquiv P S q v).1 = Sum.inr ⟨q,v⟩ := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
