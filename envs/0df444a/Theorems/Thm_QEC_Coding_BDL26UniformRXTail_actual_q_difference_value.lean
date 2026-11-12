-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_difference_value
-- name    : QEC.Coding.BDL26UniformRXTail.actual_q_difference_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:28:34.296844+00:00
-- url     : https://prove2.me/theorems/aabaa53c-8ec2-42af-a8c8-5183d6089ee4
-- title:
--   BDL26 Uniform RXTail: actual q difference value
-- statement:
--   Includes both copies of every actual Q-cylinder vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L214-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L214-L220

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_q_difference_value (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q)
    (v : QDoubleCylinderVertex (state S (2 * j + 2)).presentation q S) :
    let p := rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q v
    actualQCorrection S j q p + actualQWord S j q p = actualConstants S j q := by sorry
