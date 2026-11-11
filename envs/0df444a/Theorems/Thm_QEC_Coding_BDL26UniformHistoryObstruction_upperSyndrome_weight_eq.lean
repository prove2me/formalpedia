-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndrome_weight_eq
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperSyndrome_weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:37.581852+00:00
-- url     : https://prove2.me/theorems/61ddcdf4-7723-4960-b175-3dce4ee5667f
-- title:
--   BDL26 Uniform History Obstruction: upper Syndrome weight eq
-- statement:
--   The indexed canonical upper syndrome has exactly the lower word's weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L109-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L109-L118

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperSyndrome_weight_eq (S : OddScale) (j : Nat) :
    HammingWeight (upperSyndrome S j).val = HammingWeight (lowerSyndrome S j).val := by sorry
