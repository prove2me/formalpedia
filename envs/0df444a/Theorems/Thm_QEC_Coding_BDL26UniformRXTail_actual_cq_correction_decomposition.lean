-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_correction_decomposition
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cq_correction_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:13:00.442399+00:00
-- url     : https://prove2.me/theorems/8d11a3fe-bc6b-4cc3-ab41-4bd2d53b54dc
-- title:
--   BDL26 Uniform RXTail: actual cq correction decomposition
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual cq correction decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L229-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L229-L238

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cq_correction_decomposition (S : OddScale) (j : Nat) :
    cqCorrectionTotal (tailData S j) (lowerSyndrome S j).val =
      ∑ q, extendWordLinear
        ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (actualQCorrection S j q) := by sorry
