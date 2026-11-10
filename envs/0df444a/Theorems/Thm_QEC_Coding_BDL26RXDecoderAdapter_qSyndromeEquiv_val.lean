-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:54:34.803668+00:00
-- url     : https://prove2.me/theorems/99cfcbb5-6f38-48a2-98d3-2e74b2643d10
-- title:
--   BDL26 RXDecoder Adapter: q Syndrome Equiv val
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Syndrome Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L140-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L140-L142

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    (qSyndromeEquiv P S q e).1 = Sum.inl (Sum.inr ⟨q,e⟩) := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
