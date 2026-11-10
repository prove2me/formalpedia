-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_global_restriction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_global_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:12:18.80365+00:00
-- url     : https://prove2.me/theorems/c9744b80-bd0c-4f01-bd4c-b340907ae828
-- title:
--   BDL26 RXDecoder Adapter: local Cx global restriction
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx global restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L69-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L69-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_global_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (x : P.X) :
    restrictWordLinear ((localX P S).syndromeRegion x) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCx P S x).boundary2
        (restrictWordLinear ((localX P S).correctionRegion x) w) := by sorry
