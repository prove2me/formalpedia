-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzCoboundary1_extendZEdgeWord
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzCoboundary1_extendZEdgeWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:15.6932+00:00
-- url     : https://prove2.me/theorems/f2c12f11-274b-4764-95f4-b69db3de6e9a
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Coboundary1 extend ZEdge Word
-- statement:
--   An extended local Z-edge chain has exactly its extended local graph boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1582-L1592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1582-L1592

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzCoboundary1_extendZEdgeWord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (extendZEdgeWord P S z word) =
      extendZVertexWord P S z (rzCzGraphBoundary P z S word) := by sorry
