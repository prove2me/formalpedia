-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_raw_z_zero
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_raw_z_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:05:00.699292+00:00
-- url     : https://prove2.me/theorems/c10a8a83-d6d8-4dfb-88db-0bc48b70f9e8
-- title:
--   BDL26 Uniform RXTail: lower input raw z zero
-- statement:
--   Raw zero-Z boundary is established before indexed successor transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L34-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L34-L39

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

theorem QEC.Coding.BDL26UniformRXTail.lower_input_raw_z_zero (S : OddScale) (n : Nat)
    (z : (state S n).presentation.Z) (b : Fin 2) :
    rxCoboundary1 (state S n).presentation S (lowerErrorRaw S n) (Sum.inr (z,b)) = 0 := by sorry
