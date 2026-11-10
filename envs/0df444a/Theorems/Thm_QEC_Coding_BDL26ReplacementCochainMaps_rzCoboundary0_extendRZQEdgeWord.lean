-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZQEdgeWord
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzCoboundary0_extendRZQEdgeWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:48.987175+00:00
-- url     : https://prove2.me/theorems/7c1f4aef-2a0d-4d15-9cf9-450ba2fa2ebd
-- title:
--   BDL26 Replacement Cochain Maps: rz Coboundary0 extend RZQEdge Word
-- statement:
--   Degree-zero coboundary of an embedded Q-cylinder word: its two graph
--   endpoints together with the structurally pushed word in every adjacent
--   Z-cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L674-L747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L674-L747

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzCoboundary0_extendRZQEdgeWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (word : Word Field
      (QDoubleCylinderEdge (transposePresentation P) q S)) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q word) =
      extendRZQVertexWord P S q
        (graphBoundary
          (qDoubleCylinderEdgeStart (transposePresentation P) q S)
          (qDoubleCylinderEdgeEnd (transposePresentation P) q S) word) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S word)
        else 0 := by sorry
