-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cx_budget
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cx_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:32:58.145201+00:00
-- url     : https://prove2.me/theorems/219662d6-4393-48a9-9a76-469bac33f575
-- title:
--   BDL26 Uniform RXTail: actual cx budget
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual cx budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L177-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L177-L187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cx_budget (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    HammingWeight ((tailData S j).contract.support_decomposition.cxFlow x
      (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (cxComponentTotal (tailData S j) (lowerSyndrome S j).val x))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
          (lowerError S j))) := by sorry
