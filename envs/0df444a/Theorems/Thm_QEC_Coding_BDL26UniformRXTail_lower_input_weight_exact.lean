-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_weight_exact
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_weight_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T07:28:45.551203+00:00
-- url     : https://prove2.me/theorems/7e1eda0c-208e-4e76-aaad-4fef7135d341
-- title:
--   BDL26 Uniform RXTail: lower input weight exact
-- statement:
--   Exact syndrome weight is a face count, separately from error weight one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L141-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L141-L144

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

theorem QEC.Coding.BDL26UniformRXTail.lower_input_weight_exact (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) = (incidentStarFaces S n).card := by sorry
