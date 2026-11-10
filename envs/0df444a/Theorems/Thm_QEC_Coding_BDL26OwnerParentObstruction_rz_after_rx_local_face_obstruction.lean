-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rz_after_rx_local_face_obstruction
-- name    : QEC.Coding.BDL26OwnerParentObstruction.rz_after_rx_local_face_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:17:12.14936+00:00
-- url     : https://prove2.me/theorems/af77dea7-7542-4e0a-93cd-76e820a3e657
-- title:
--   BDL26 Owner Parent Obstruction: rz after rx local face obstruction
-- statement:
--   The same obstruction already occurs in degree two, without any connector
--   chain: the RZ map sends an RX local X-face to one Z root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L64-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L64-L79

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

theorem QEC.Coding.BDL26OwnerParentObstruction.rz_after_rx_local_face_obstruction
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    let z : (rxReplacementPresentation P S).Z := Sum.inl (Sum.inl ⟨x, face⟩)
    let target : RZZ (rxReplacementPresentation P S) S :=
      ⟨z, rzMap1ZRoot (rxReplacementPresentation P S) A z S⟩
    map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord z) target = 1 ∧
      rxSyndromeOwner P S z = .x x ∧
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) = none := by sorry
