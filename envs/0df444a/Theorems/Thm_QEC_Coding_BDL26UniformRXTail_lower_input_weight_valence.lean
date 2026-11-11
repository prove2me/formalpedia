-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_weight_valence
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_weight_valence
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:06:36.077041+00:00
-- url     : https://prove2.me/theorems/65528636-62d1-439c-a1c4-f92d12f3e961
-- title:
--   BDL26 Uniform RXTail: lower input weight valence
-- statement:
--   The BDL26 Uniform RXTail construction uses the lower input weight valence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L164-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L164-L170

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
open BDL26BoundedValence

theorem QEC.Coding.BDL26UniformRXTail.lower_input_weight_valence (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) =
      qZDegree (state S n).presentation (selectedNeighbor S n).val := by sorry
