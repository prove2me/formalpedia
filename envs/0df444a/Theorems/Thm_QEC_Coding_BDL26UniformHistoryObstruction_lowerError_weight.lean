-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerError_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerError_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:39:40.010337+00:00
-- url     : https://prove2.me/theorems/6aef1b44-7281-4e29-9e7a-c9b01f3d354c
-- title:
--   BDL26 Uniform History Obstruction: lower Error weight
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Error weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L114-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L114-L119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerError_weight (S : OddScale) (j : Nat) :
    HammingWeight (lowerError S j) = 1 := by sorry
