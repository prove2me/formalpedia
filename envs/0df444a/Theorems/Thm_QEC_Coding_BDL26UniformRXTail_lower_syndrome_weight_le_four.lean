-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_syndrome_weight_le_four
-- name    : QEC.Coding.BDL26UniformRXTail.lower_syndrome_weight_le_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:07:28.98388+00:00
-- url     : https://prove2.me/theorems/aee7bd57-0deb-4da2-ac3d-bb672c5cb8fe
-- title:
--   BDL26 Uniform RXTail: lower syndrome weight le four
-- statement:
--   The BDL26 Uniform RXTail construction uses the lower syndrome weight le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L196-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L196-L204

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

theorem QEC.Coding.BDL26UniformRXTail.lower_syndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by sorry
