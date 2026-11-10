-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzWholeFace_four_sides
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzWholeFace_four_sides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:46.626435+00:00
-- url     : https://prove2.me/theorems/b38c82db-f424-40ab-be7b-685edd0c4fb7
-- title:
--   BDL26 Replacement Cochain Maps: rz Whole Face four sides
-- statement:
--   A whole copied face contributes its two radial connector arms and its
--   two outer Q-cylinder arms, without any interior edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1574-L1604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1574-L1604

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzWholeFace_four_sides
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (z : P.Z)
    (owner : RZOldFaceOver P x z) :
    extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
      (subdivisionBoundary2 (transposePresentation P) z S
        (subdivisionWholeFaceChain (transposePresentation P) z S
          (rzOldFaceOverZStarFace P x z owner))) =
      ∑ corner : Two,
        ((∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, Sum.inl
            (xStarFaceXQEdge (transposePresentation P) z
              (rzOldFaceOverZStarFace P x z owner) corner, i)) :
            ZDoubleCylinderEdge P z S)) +
        (∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, Sum.inl
            (xStarFaceQZEdge (transposePresentation P) z
              (rzOldFaceOverZStarFace P x z owner) corner, i)) :
            ZDoubleCylinderEdge P z S))) := by sorry
