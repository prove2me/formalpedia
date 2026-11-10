-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxConnectingXQ1_apply_q
-- name    : QEC.Coding.BDL26ReplacementSupport.rxConnectingXQ1_apply_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:11.017185+00:00
-- url     : https://prove2.me/theorems/1496dcc3-1da4-40c3-aa5a-ffa59dc1b61a
-- title:
--   BDL26 Replacement Support: rx Connecting XQ1 apply q
-- statement:
--   The X-to-Q matrix term is the sum of the actual adjacent edge restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L484-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L484-L504

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

theorem QEC.Coding.BDL26ReplacementSupport.rxConnectingXQ1_apply_q
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (word : Word Field (RX1 P S)) (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxConnectingXQ1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      ∑ x : P.X, if hxq : P.xq x q = true then
        rxXQDegreeOne P A q x hxq S
          (fun localEdge => word (Sum.inl ⟨x, localEdge⟩)) edge else 0 := by sorry
