-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_inputSpot_injective
-- name    : QEC.Coding.BDL26UniformRXTail.inputSpot_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:05:29.027114+00:00
-- url     : https://prove2.me/theorems/7f96bd2d-c621-43d0-9c78-236eefea3ff7
-- title:
--   BDL26 Uniform RXTail: input Spot injective
-- statement:
--   The BDL26 Uniform RXTail construction uses the input Spot injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L136-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L136-L138

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

theorem QEC.Coding.BDL26UniformRXTail.inputSpot_injective (S : OddScale) (n : Nat) : Function.Injective (inputSpot S n) := by sorry
