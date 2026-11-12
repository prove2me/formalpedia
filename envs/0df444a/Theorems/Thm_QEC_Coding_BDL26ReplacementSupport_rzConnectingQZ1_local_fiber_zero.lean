-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzConnectingQZ1_local_fiber_zero
-- name    : QEC.Coding.BDL26ReplacementSupport.rzConnectingQZ1_local_fiber_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:59:41.023448+00:00
-- url     : https://prove2.me/theorems/f8e9cb34-1964-4df6-807b-f13e1b5c3bbb
-- title:
--   BDL26 Replacement Support: rz Connecting QZ1 local fiber zero
-- statement:
--   The connecting RZ term vanishes on an actual local Z fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L394-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L394-L404

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rzConnectingQZ1_local_fiber_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (z : P.Z) (word : Word Field (RZQ P S)) :
    rzConnectingQZ1 P A S (fiberPart (rzCorrectionOwner P S) (.z z) word) = 0 := by sorry
