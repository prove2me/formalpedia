-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_layer
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:27:53.480541+00:00
-- url     : https://prove2.me/theorems/f4266e8b-ff56-4ee8-94cb-149804084fc9
-- title:
--   BDL26 Uniform RXTail: lower input layer
-- statement:
--   Exact selected-copy and origin-cell formula, before counting support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L42-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L42-L70

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

theorem QEC.Coding.BDL26UniformRXTail.lower_input_layer (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n))
    (copy : Fin 2) (i j : Fin S.half) :
    lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n, .inl (copy, face, i, j)⟩)) =
      if copy = 0 ∧ i.val = 0 ∧ j.val = 0 ∧ incidentStarFace S n face then 1 else 0 := by sorry
