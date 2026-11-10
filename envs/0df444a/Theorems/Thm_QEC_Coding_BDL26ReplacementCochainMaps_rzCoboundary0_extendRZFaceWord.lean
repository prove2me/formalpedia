-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZFaceWord
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzCoboundary0_extendRZFaceWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:31.862204+00:00
-- url     : https://prove2.me/theorems/202284ef-ce87-4432-b581-b4f6da862f62
-- title:
--   BDL26 Replacement Cochain Maps: rz Coboundary0 extend RZFace Word
-- statement:
--   The successor X-Q coboundary of an embedded local face word is exactly
--   the embedded quotient-free face boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1302-L1412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1302-L1412

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzCoboundary0_extendRZFaceWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderFace P z S)) :
    rzCoboundary0 P A4 S (extendRZFaceWord P S z word) =
      extendRZLocalEdgeWord P S z
        (doubleCylinderBoundary2 (transposePresentation P) z S word) := by sorry
