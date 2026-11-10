-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0QRay_boundary
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:11.297199+00:00
-- url     : https://prove2.me/theorems/416545be-1ab4-4e39-a90e-74ce05d72f9c
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 QRay boundary
-- statement:
--   Cancellation of adjacent subdivision endpoints leaves the arm's root and
--   terminal vertex by finite enumeration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L989-L1027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L989-L1027

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_boundary
    (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    graphBoundary
        (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
        (rzMap0QRay P S x q hxq) =
      canonicalBasisWord (rzMap1QRoot P q S) +
        canonicalBasisWord (rzXQVertex P q x hxq S 0) := by sorry
