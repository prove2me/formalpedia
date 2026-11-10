-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rz_after_rx_local_edge_obstruction
-- name    : QEC.Coding.BDL26OwnerParentObstruction.rz_after_rx_local_edge_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:47.626879+00:00
-- url     : https://prove2.me/theorems/dbb6a104-8ed3-4800-94da-5bd9a61d1c3a
-- title:
--   BDL26 Owner Parent Obstruction: rz after rx local edge obstruction
-- statement:
--   An RX local X-edge survives the next RZ map at its distinguished Q root,
--   although its upper local label has no adjacent graph parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L46-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L46-L60

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

theorem QEC.Coding.BDL26OwnerParentObstruction.rz_after_rx_local_edge_obstruction
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    let q : (rxReplacementPresentation P S).Q := Sum.inl ⟨x, edge⟩
    let target : RZQ (rxReplacementPresentation P S) S :=
      Sum.inr ⟨q, rzMap1QRoot (rxReplacementPresentation P S) q S⟩
    map1Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord q) target = 1 ∧
      rxCorrectionOwner P S q = .x x ∧
      rxParent P S (rzCorrectionOwner (rxReplacementPresentation P S) S target) = none := by sorry
