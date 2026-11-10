-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendXCorrection_delta_at_x
-- name    : QEC.Coding.BDL26OwnerParentObstruction.extendXCorrection_delta_at_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:25:35.1164+00:00
-- url     : https://prove2.me/theorems/7cebed35-6668-45b2-ae75-674d739d7ced
-- title:
--   BDL26 Owner Parent Obstruction: extend XCorrection delta at x
-- statement:
--   The local coboundary is retained exactly on the selected X block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L228-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L228-L237

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

theorem QEC.Coding.BDL26OwnerParentObstruction.extendXCorrection_delta_at_x (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (e : Word BDL26Field (DoubleCylinderEdge P x S))
    (face : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (rxBoundary2 P S) (extendXCorrection P S x e)
      (.inl (.inl ⟨x,face⟩)) = wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e face := by sorry
