-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_outgoing_sum_zero
-- name    : QEC.Coding.BDL26UniformRXTail.actual_q_outgoing_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:35:59.111195+00:00
-- url     : https://prove2.me/theorems/0b019f84-ab06-42f6-9841-6507d4664236
-- title:
--   BDL26 Uniform RXTail: actual q outgoing sum zero
-- statement:
--   Aggregate outgoing cancellation, retaining every Q owner and both copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L326-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L326-L337

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_q_outgoing_sum_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (∑ q, (tailData S j).contract.support_decomposition.cqFlow q (actualQWord S j q))
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by sorry
