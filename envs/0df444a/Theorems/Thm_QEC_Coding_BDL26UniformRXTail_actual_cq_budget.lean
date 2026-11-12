-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_budget
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cq_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:09:36.70814+00:00
-- url     : https://prove2.me/theorems/e755a7c2-9af3-4819-8e2e-782e7d338fab
-- title:
--   BDL26 Uniform RXTail: actual cq budget
-- statement:
--   The actual CQ choice satisfies its full outgoing budget, with no supplied witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L142-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L142-L149

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cq_budget (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    HammingWeight ((tailData S j).contract.support_decomposition.cqFlow q
      (restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (cqComponentTotal (tailData S j) (lowerSyndrome S j).val q))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by sorry
