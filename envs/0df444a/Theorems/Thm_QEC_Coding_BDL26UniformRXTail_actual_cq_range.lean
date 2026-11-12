-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_range
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:54:13.105752+00:00
-- url     : https://prove2.me/theorems/ec689020-fbef-4e3c-a743-d8d8f43e53ac
-- title:
--   BDL26 Uniform RXTail: actual cq range
-- statement:
--   Range recovery uses zero X ERROR restrictions of the constructed error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L115-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L115-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cq_range (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    CqLocalRangeAt (tailData S j) (lowerSyndrome S j).val q := by sorry
