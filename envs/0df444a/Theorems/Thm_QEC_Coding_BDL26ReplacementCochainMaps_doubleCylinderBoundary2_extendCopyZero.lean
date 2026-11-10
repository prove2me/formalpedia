-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_doubleCylinderBoundary2_extendCopyZero
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.doubleCylinderBoundary2_extendCopyZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:04.598744+00:00
-- url     : https://prove2.me/theorems/15aae5c2-060f-4188-8d9b-f5d9b9a51794
-- title:
--   BDL26 Replacement Cochain Maps: double Cylinder Boundary2 extend Copy Zero
-- statement:
--   Copy-zero extension intertwines the small-grid boundary with the
--   quotient-free double-cylinder boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1256-L1280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1256-L1280

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.doubleCylinderBoundary2_extendCopyZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (SubdivisionFace P x S)) :
    doubleCylinderBoundary2 P x S
        (extendCopyZeroSubdivisionFaceWord P x S word) =
      extendCopyZeroSubdivisionEdgeWord P x S
        (subdivisionBoundary2 P x S word) := by sorry
