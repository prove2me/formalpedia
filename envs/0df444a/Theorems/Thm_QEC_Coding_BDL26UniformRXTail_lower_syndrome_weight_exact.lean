-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_syndrome_weight_exact
-- name    : QEC.Coding.BDL26UniformRXTail.lower_syndrome_weight_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:27:28.254059+00:00
-- url     : https://prove2.me/theorems/e5db138e-a283-4723-a60f-0387a4a827ee
-- title:
--   BDL26 Uniform RXTail: lower syndrome weight exact
-- statement:
--   The BDL26 Uniform RXTail construction uses the lower syndrome weight exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L186-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L186-L194

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

theorem QEC.Coding.BDL26UniformRXTail.lower_syndrome_weight_exact (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val = (incidentStarFaces S (2 * j + 2)).card := by sorry
