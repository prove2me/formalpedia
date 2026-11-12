-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_other_owner
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_other_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:17:59.74656+00:00
-- url     : https://prove2.me/theorems/600a2b7b-1102-40f5-9cef-9c4a29ae9060
-- title:
--   BDL26 Uniform RXTail: lower input other owner
-- statement:
--   The BDL26 Uniform RXTail construction uses the lower input other owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L26-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L26-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformRXTail.lower_input_other_owner (S : OddScale) (n : Nat)
    (z : RX2 (state S n).presentation S)
    (hz : rxSyndromeOwner (state S n).presentation S z ≠ .x (retainedX S n)) :
    lowerSyndromeRaw S n z = 0 := by sorry
