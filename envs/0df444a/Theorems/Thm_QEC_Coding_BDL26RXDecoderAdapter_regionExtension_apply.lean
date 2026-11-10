-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
-- name    : QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:10:21.235383+00:00
-- url     : https://prove2.me/theorems/b9141fa7-7f9f-4d7e-8849-774a83f4c26f
-- title:
--   BDL26 RXDecoder Adapter: region Extension apply
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the region Extension apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L23-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L23-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (w : Word BDL26Field (LocalRegionIndex Y)) (p : A) :
    extendWordLinear Y w p = extendLocalSignal Y w p := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply
