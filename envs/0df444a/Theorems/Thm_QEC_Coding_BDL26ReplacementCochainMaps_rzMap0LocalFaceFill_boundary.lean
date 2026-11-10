-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0LocalFaceFill_boundary
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0LocalFaceFill_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:40:38.202104+00:00
-- url     : https://prove2.me/theorems/7600084d-75c7-4f6b-b71d-743cb6e34d10
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 Local Face Fill boundary
-- statement:
--   Coboundary of the explicit local filling is the sum of the four outer
--   subdivision sides of every old face over the requested X/Z pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1693-L1708
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1693-L1708

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0LocalFaceFill_boundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (z : P.Z) :
    rzCoboundary0 P A4 S (rzMap0LocalFaceFill P S x z) =
      ∑ owner : RZOldFaceOver P x z,
        extendRZLocalEdgeWord P S z
          (extendCopyZeroSubdivisionEdgeWord (transposePresentation P) z S
            (subdivisionBoundary2 (transposePresentation P) z S
              (subdivisionWholeFaceChain (transposePresentation P) z S
                (rzOldFaceOverZStarFace P x z owner)))) := by sorry
