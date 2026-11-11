-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerErrorRaw_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerErrorRaw_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:31:30.744757+00:00
-- url     : https://prove2.me/theorems/f5b8d367-0144-4ea7-ae1f-404bb6d02f26
-- title:
--   BDL26 Uniform History Obstruction: lower Error Raw weight
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Error Raw weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L101-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L101-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerErrorRaw_weight (S : OddScale) (n : Nat) :
    HammingWeight (lowerErrorRaw S n) = 1 := by sorry
