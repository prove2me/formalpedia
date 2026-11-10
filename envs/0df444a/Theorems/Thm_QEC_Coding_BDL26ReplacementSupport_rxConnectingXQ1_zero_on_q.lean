-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxConnectingXQ1_zero_on_q
-- name    : QEC.Coding.BDL26ReplacementSupport.rxConnectingXQ1_zero_on_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:18:54.057189+00:00
-- url     : https://prove2.me/theorems/8c1093db-a25c-4c9f-9093-14567fcecce4
-- title:
--   BDL26 Replacement Support: rx Connecting XQ1 zero on q
-- statement:
--   A local Q correction cannot create an X-to-Q connecting contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L247-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L247-L257

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

theorem QEC.Coding.BDL26ReplacementSupport.rxConnectingXQ1_zero_on_q (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (hX : ∀ xe, word (Sum.inl xe) = 0) :
    rxConnectingXQ1 P S word = 0 := by sorry
