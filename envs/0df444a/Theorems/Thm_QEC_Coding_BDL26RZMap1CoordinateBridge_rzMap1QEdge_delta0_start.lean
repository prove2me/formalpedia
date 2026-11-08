-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_start
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1QEdge_delta0_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:20.928346+00:00
-- url     : https://prove2.me/theorems/b796dce4-0aa0-4838-8d29-ba14ca634cb8
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Map1 QEdge delta0 start
-- statement:
--   The positive start-endpoint coordinate of the typed δ0 basis equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1333-L1344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1333-L1344

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1QEdge_delta0_start
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    tannerCoboundary0
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (rzMap1QEdgeX P S q edge))
        (Sum.inr ⟨q, qDoubleCylinderEdgeStart
          (transposePresentation P) q S edge⟩) = 1 := by sorry
