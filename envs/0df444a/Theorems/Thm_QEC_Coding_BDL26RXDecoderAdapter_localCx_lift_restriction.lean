-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_lift_restriction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_lift_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:23.942135+00:00
-- url     : https://prove2.me/theorems/6c7da311-e3ed-4ab9-8bd0-605b983fdda4
-- title:
--   BDL26 RXDecoder Adapter: local Cx lift restriction
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx lift restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L62-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L62-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_lift_restriction (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S)) :
    restrictWordLinear ((localX P S).correctionRegion x) (rxCoboundary0 P S (xLift P S x w)) =
      wordLinearMapTranspose (localCx P S x).boundary1 w := by sorry
