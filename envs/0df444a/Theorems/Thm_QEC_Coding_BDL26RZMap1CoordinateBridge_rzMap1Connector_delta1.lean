-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1Connector_delta1
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_delta1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:17:57.391251+00:00
-- url     : https://prove2.me/theorems/68b2f180-0c67-48f9-95a0-ceffc8dd2d47
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Map1 Connector delta1
-- statement:
--   The connecting cochain has exactly the fixed Z root and embedded Q root
--   as its local degree-one coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1362-L1375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1362-L1375

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_delta1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzCzGraphBoundary P z S (rzMap1Connector P A4 q z hqz S) =
      canonicalBasisWord (rzMap1ZRoot P A4 z S) +
        canonicalBasisWord
          (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)) := by sorry
