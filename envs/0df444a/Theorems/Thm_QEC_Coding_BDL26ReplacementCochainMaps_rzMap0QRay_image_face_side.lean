-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0QRay_image_face_side
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_image_face_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:19.635194+00:00
-- url     : https://prove2.me/theorems/78ffdbd7-4b9b-4e4b-a745-d8a571f83029
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 QRay image face side
-- statement:
--   The Q-cylinder arm embeds as the corresponding outer Q-Z side of an
--   incident transposed face.  All segments retain their original incidence tag.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1541-L1570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1541-L1570

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_image_face_side
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) (corner : Two)
    (hxq : P.xq x (P.faceQ owner.1 corner) = true)
    (hqz : P.qz (P.faceQ owner.1 corner) z = true) :
    rzQZDegreeZero P A (P.faceQ owner.1 corner) z hqz S
        (rzMap0QRay P S x (P.faceQ owner.1 corner) hxq) =
      ∑ i : Fin S.half, canonicalBasisWord
        (Sum.inl (0, Sum.inl
          (xStarFaceQZEdge (transposePresentation P) z
            (rzOldFaceOverZStarFace P x z owner) corner, i)) :
          ZDoubleCylinderEdge P z S) := by sorry
