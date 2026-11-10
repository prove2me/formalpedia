-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
-- name    : QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:54:32.61762+00:00
-- url     : https://prove2.me/theorems/d4d631a7-3852-4408-9e4e-941bc70c97bc
-- title:
--   BDL26 RXDecoder Adapter: z Syndrome Equiv val
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the z Syndrome Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L144-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Regions.lean#L144-L145

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (c : Fin 2) : (zSyndromeEquiv P S z c).1 = Sum.inr (z,c) := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val
