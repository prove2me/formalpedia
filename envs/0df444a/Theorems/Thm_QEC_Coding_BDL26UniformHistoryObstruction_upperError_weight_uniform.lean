-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperError_weight_uniform
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperError_weight_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:40:59.754084+00:00
-- url     : https://prove2.me/theorems/3ad7adfd-7e71-47a5-83ff-1f0674f7bf07
-- title:
--   BDL26 Uniform History Obstruction: upper Error weight uniform
-- statement:
--   A measured actual incidence bound gives a depth-independent upper error budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L197-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L197-L203

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperError_weight_uniform (S : OddScale) (j : Nat) :
    HammingWeight (upperError S j) ≤ 2 * S.ell - 1 := by sorry
