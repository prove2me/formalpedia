-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0_all_face_boundaries
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0_all_face_boundaries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:40:49.087514+00:00
-- url     : https://prove2.me/theorems/c0b8adf6-6175-4d22-a97d-fe684677ab54
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 all face boundaries
-- statement:
--   Sum the exact face boundaries by their incident Q coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1740-L1772
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1740-L1772

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0_all_face_boundaries
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) :
    (∑ z : P.Z, rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z)) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzMap1Connector P A4 q z hqz S +
              rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
                (rzMap0QRay P S x q hxq))
        else 0
      else 0 := by sorry
