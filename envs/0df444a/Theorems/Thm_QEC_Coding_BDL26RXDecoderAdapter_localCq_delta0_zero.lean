-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta0_zero
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_delta0_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:31.958136+00:00
-- url     : https://prove2.me/theorems/f9077824-b88a-4bb3-8ba1-6c9eafaea2c4
-- title:
--   BDL26 RXDecoder Adapter: local Cq delta0 zero
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cq delta0 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L89-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L89-L95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_delta0_zero (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    wordLinearMapTranspose (localCq P S q).boundary1 = 0 := by sorry
