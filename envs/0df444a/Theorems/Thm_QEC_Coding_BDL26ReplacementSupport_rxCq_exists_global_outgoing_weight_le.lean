-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxCq_exists_global_outgoing_weight_le
-- name    : QEC.Coding.BDL26ReplacementSupport.rxCq_exists_global_outgoing_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:36:37.829362+00:00
-- url     : https://prove2.me/theorems/0467bc0b-5366-4bd8-949c-6bbfb5bc7da5
-- title:
--   BDL26 Replacement Support: rx Cq exists global outgoing weight le
-- statement:
--   Exact F12 Q-local correction with the budget over every old-Z label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L469-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L469-L481

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

theorem QEC.Coding.BDL26ReplacementSupport.rxCq_exists_global_outgoing_weight_le
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range
      (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ correction : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) correction = syndrome ∧
        (∑ z : P.Z, HammingWeight (rxQOutgoing P q S correction z)) ≤
          HammingWeight syndrome := by sorry
