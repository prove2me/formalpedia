-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxLocalDelta1_apply_q
-- name    : QEC.Coding.BDL26ReplacementSupport.rxLocalDelta1_apply_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:17:16.241818+00:00
-- url     : https://prove2.me/theorems/bf0c90bd-bebe-4b8f-b34a-f108c516712e
-- title:
--   BDL26 Replacement Support: rx Local Delta1 apply q
-- statement:
--   The shifted Q diagonal block is its concrete local graph coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L556-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L556-L570

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

theorem QEC.Coding.BDL26ReplacementSupport.rxLocalDelta1_apply_q
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field (RX1 P S))
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxLocalDelta1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => word (Sum.inr ⟨q, vertex⟩)) edge := by sorry
