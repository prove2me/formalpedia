-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_correction_constant
-- name    : QEC.Coding.BDL26UniformRXTail.actual_q_correction_constant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:14:40.112842+00:00
-- url     : https://prove2.me/theorems/d1609d04-f50a-4413-ac5e-d34dd4290917
-- title:
--   BDL26 Uniform RXTail: actual q correction constant
-- statement:
--   The CQ budget is the budget of the explicit h-plus-constant correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L356-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L356-L365

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_q_correction_constant (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    actualQCorrection S j q = actualQWord S j q + (fun _ => actualConstants S j q) := by sorry
