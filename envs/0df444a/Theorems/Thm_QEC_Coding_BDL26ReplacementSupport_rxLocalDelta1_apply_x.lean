-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxLocalDelta1_apply_x
-- name    : QEC.Coding.BDL26ReplacementSupport.rxLocalDelta1_apply_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:16:27.770845+00:00
-- url     : https://prove2.me/theorems/65e275d4-15e3-4e86-9d72-61309304ee80
-- title:
--   BDL26 Replacement Support: rx Local Delta1 apply x
-- statement:
--   The X diagonal block is its concrete local cellular coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L539-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L539-L553

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

theorem QEC.Coding.BDL26ReplacementSupport.rxLocalDelta1_apply_x
    (P : TannerSquarePresentation) (S : OddScale) (word : Word Field (RX1 P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    rxLocalDelta1 P S word (Sum.inl (Sum.inl ⟨x, face⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun edge => word (Sum.inl ⟨x, edge⟩)) face := by sorry
