-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxConnectingQZ1_zero_on_x
-- name    : QEC.Coding.BDL26ReplacementSupport.rxConnectingQZ1_zero_on_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:18:12.658196+00:00
-- url     : https://prove2.me/theorems/11fb37e7-acd4-4958-ab12-4da6bed7a96d
-- title:
--   BDL26 Replacement Support: rx Connecting QZ1 zero on x
-- statement:
--   A local X correction cannot create a direct Z-block syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L234-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L234-L244

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

theorem QEC.Coding.BDL26ReplacementSupport.rxConnectingQZ1_zero_on_x (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (hQ : ∀ qv, word (Sum.inr qv) = 0) :
    rxConnectingQZ1 P S word = 0 := by sorry
