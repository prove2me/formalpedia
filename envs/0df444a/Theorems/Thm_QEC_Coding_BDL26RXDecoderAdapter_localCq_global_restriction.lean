-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_global_restriction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_global_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:48:57.631539+00:00
-- url     : https://prove2.me/theorems/d54de50b-d034-4225-86f6-13f13f563606
-- title:
--   BDL26 RXDecoder Adapter: local Cq global restriction
-- statement:
--   This premise is zero actual X error, as required by the connecting block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L80-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L80-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_global_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) (q : P.Q) :
    restrictWordLinear ((localQ P S).syndromeRegion q) (rxCoboundary1 P S w) =
      wordLinearMapTranspose (localCq P S q).boundary2
        (restrictWordLinear ((localQ P S).correctionRegion q) w) := by sorry
