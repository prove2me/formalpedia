-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_boundary
-- name    : QEC.Coding.BDL26UniformRXTail.cleanedError_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:43:16.449166+00:00
-- url     : https://prove2.me/theorems/f8cfffe2-67c4-4833-978d-e06a761ec388
-- title:
--   BDL26 Uniform RXTail: cleaned Error boundary
-- statement:
--   The BDL26 Uniform RXTail construction uses the cleaned Error boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L105-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L105-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.cleanedError_boundary (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (cleanedError S j) =
      rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val := by sorry
