-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_support
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:05:15.786333+00:00
-- url     : https://prove2.me/theorems/dc8450c8-88c8-4d67-b151-d2f5e4beed34
-- title:
--   BDL26 Uniform RXTail: lower input support
-- statement:
--   The BDL26 Uniform RXTail construction uses the lower input support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L98-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L98-L134

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

theorem QEC.Coding.BDL26UniformRXTail.lower_input_support (S : OddScale) (n : Nat) :
    hammingSupport (lowerSyndromeRaw S n) =
      (incidentStarFaces S n).image (inputSpot S n) := by sorry
