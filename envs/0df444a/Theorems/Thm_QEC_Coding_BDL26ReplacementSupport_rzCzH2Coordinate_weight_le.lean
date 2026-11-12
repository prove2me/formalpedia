-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzCzH2Coordinate_weight_le
-- name    : QEC.Coding.BDL26ReplacementSupport.rzCzH2Coordinate_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:59:19.432918+00:00
-- url     : https://prove2.me/theorems/0607c8aa-1127-4acc-acc3-2db99057b01c
-- title:
--   BDL26 Replacement Support: rz Cz H2 Coordinate weight le
-- statement:
--   The bound is the existing RZ cohomology coordinate applied to an actual
--   syndrome representative, expressed as its single finite output coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L313-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L313-L325

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

theorem QEC.Coding.BDL26ReplacementSupport.rzCzH2Coordinate_weight_le
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (syndrome : Word Field (ZDoubleCylinderVertex P z S)) :
    HammingWeight (fun _ : Unit => rzCzH2Coordinate P z S
      ((LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ syndrome)) ≤
        HammingWeight syndrome := by sorry
