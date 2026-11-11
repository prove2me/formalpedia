-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndrome_weight_le_four
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperSyndrome_weight_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:18.832847+00:00
-- url     : https://prove2.me/theorems/9c8a270f-f66d-400b-81f0-5c7d8668ae06
-- title:
--   BDL26 Uniform History Obstruction: upper Syndrome weight le four
-- statement:
--   The uniform input's syndrome bound is independent of scale and depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L121-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L121-L124

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperSyndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (upperSyndrome S j).val ≤ 4 := by sorry
