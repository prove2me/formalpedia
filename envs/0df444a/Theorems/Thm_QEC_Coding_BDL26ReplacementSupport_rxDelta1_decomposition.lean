-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxDelta1_decomposition
-- name    : QEC.Coding.BDL26ReplacementSupport.rxDelta1_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:16:11.312599+00:00
-- url     : https://prove2.me/theorems/11748a3c-0a7e-41a4-a662-dd080fdd8e1e
-- title:
--   BDL26 Replacement Support: rx Delta1 decomposition
-- statement:
--   The total degree-one coboundary has precisely the audited local and two
--   adjacent connecting terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L225-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L225-L231

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rxDelta1_decomposition (P : TannerSquarePresentation) (S : OddScale) :
    wordLinearMapTranspose (rxBoundary2 P S) =
      rxLocalDelta1 P S + rxConnectingXQ1 P S + rxConnectingQZ1 P S := by sorry
