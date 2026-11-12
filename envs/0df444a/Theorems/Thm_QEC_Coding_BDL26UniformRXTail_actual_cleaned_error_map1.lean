-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cleaned_error_map1
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cleaned_error_map1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:15:13.498188+00:00
-- url     : https://prove2.me/theorems/fb81fbaa-d1b3-435a-b7bd-2604972496ab
-- title:
--   BDL26 Uniform RXTail: actual cleaned error map1
-- statement:
--   A literal error identity, stronger than existence of an unspecified coarse preimage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L241-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L241-L253

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cleaned_error_map1 (S : OddScale) (j : Nat) :
    cleanedError S j + cqCorrectionTotal (tailData S j) (lowerSyndrome S j).val =
      ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).map1 (actualConstants S j) := by sorry
