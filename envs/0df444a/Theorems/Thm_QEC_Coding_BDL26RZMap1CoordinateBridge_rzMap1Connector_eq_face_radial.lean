-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1Connector_eq_face_radial
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_eq_face_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:25.981207+00:00
-- url     : https://prove2.me/theorems/94233899-0090-4af4-8574-684ad0691829
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Map1 Connector eq face radial
-- statement:
--   The selected connector traverses the radial side to its old-Q vertex.
--   Any incident face gives the same tagged original-edge chain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L598-L642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L598-L642

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_eq_face_radial
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (face : XStarFace (transposePresentation P) z) (corner : Two)
    (hcorner : P.faceQ face.1 corner = q) :
    rzMap1Connector P A4 q z hqz S =
      ∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, Sum.inl
          (xStarFaceXQEdge (transposePresentation P) z face corner, i)) :
            ZDoubleCylinderEdge P z S) := by sorry
