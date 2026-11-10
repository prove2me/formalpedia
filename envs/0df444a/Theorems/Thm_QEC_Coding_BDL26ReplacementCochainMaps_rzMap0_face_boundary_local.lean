-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0_face_boundary_local
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0_face_boundary_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:40:25.533234+00:00
-- url     : https://prove2.me/theorems/af300ffd-2959-4b67-b39e-54cd7f545edf
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 face boundary local
-- statement:
--   The boundary of the chosen face fillings is precisely the connector sum
--   plus the embedded Q-arm sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1632-L1678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1632-L1678

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0_face_boundary_local
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z) :
    (∑ owner : RZOldFaceOver P x z,
      extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
        (subdivisionBoundary2 (transposePresentation P) z S
          (subdivisionWholeFaceChain (transposePresentation P) z S
            (rzOldFaceOverZStarFace P x z owner)))) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        if hqz : P.qz q z = true then
          rzMap1Connector P A4 q z hqz S +
            rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QRay P S x q hxq)
        else 0
      else 0 := by sorry
