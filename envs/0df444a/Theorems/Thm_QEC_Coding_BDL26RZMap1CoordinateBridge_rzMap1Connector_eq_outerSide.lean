-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1Connector_eq_outerSide
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_eq_outerSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:13.236006+00:00
-- url     : https://prove2.me/theorems/8e6196ce-d635-4e3c-ac02-2dc10e407e94
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz Map1 Connector eq outer Side
-- statement:
--   The constructed connector is exactly the explicit outer-side chain of its
--   public V4 owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L504-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L504-L594

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_eq_outerSide
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzMap1Connector P A4 q z hqz S =
      rzMap1ConnectorOuterSide P A4 q z hqz S := by sorry
