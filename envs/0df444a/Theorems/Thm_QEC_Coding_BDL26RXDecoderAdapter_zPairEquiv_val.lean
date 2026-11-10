-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zPairEquiv_val
-- name    : QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:57:01.738251+00:00
-- url     : https://prove2.me/theorems/215017dc-7592-49e8-a6c8-e63326a9ea1a
-- title:
--   BDL26 RXDecoder Adapter: z Pair Equiv val
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the z Pair Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L134-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L134-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val (P : TannerSquarePresentation) (S : OddScale)
    (p : P.Z × Fin 2) : (zPairEquiv P S p).val = Sum.inr p := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val
