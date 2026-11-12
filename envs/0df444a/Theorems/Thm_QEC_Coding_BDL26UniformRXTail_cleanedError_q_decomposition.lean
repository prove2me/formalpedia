-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_q_decomposition
-- name    : QEC.Coding.BDL26UniformRXTail.cleanedError_q_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:28:25.954724+00:00
-- url     : https://prove2.me/theorems/8f77e57b-c1df-4745-940e-092534b8bfd3
-- title:
--   BDL26 Uniform RXTail: cleaned Error q decomposition
-- statement:
--   The BDL26 Uniform RXTail construction uses the cleaned Error q decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L162-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L162-L175

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.cleanedError_q_decomposition (S : OddScale) (j : Nat) :
    cleanedError S j = ∑ q, extendWordLinear
      ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (actualQWord S j q) := by sorry
