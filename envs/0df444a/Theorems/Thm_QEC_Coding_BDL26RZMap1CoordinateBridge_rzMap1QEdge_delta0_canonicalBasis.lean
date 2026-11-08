-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_canonicalBasis
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1QEdge_delta0_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:45.99598+00:00
-- url     : https://prove2.me/theorems/590b725f-3a79-4c58-8b4a-782c7fd4ddf1
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Map1 QEdge delta0 canonical Basis
-- statement:
--   Typed canonical-basis δ0 equation for the concrete Q-edge gluing row.
--   This exposes the actual two Q endpoints and every adjacent Z-edge image; it
--   does not assemble the downstream full cochain map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1304-L1330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1304-L1330

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1QEdge_delta0_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    tannerCoboundary0
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge)) =
      rzMap1QEdgeDelta0BasisImage P A4 S q edge := by sorry
