-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperError_weight_le
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.upperError_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:31:58.120965+00:00
-- url     : https://prove2.me/theorems/cd730316-ec90-43b4-acb8-625701fa5946
-- title:
--   BDL26 Uniform History Obstruction: upper Error weight le
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the upper Error weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L184-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L184-L194

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.upperError_weight_le (S : OddScale) (j : Nat) :
    HammingWeight (upperError S j) ≤
      1 + qZDegree (state S (2 * j + 3)).presentation (lowerBasis S j) * S.half := by sorry
