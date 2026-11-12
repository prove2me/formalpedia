-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_constant_budget
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cq_constant_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:13:35.724007+00:00
-- url     : https://prove2.me/theorems/08411349-7ff4-4e45-86f4-be1c4004fa39
-- title:
--   BDL26 Uniform RXTail: actual cq constant budget
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual cq constant budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L367-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L367-L373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cq_constant_budget (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    HammingWeight ((tailData S j).contract.support_decomposition.cqFlow q
      (actualQWord S j q + (fun _ => actualConstants S j q))) ≤
    HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by sorry
