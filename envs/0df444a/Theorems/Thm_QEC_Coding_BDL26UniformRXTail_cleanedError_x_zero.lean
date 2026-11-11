-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_x_zero
-- name    : QEC.Coding.BDL26UniformRXTail.cleanedError_x_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T06:53:58.514408+00:00
-- url     : https://prove2.me/theorems/d01b16d6-4331-4440-926e-a0ee62493a86
-- title:
--   BDL26 Uniform RXTail: cleaned Error x zero
-- statement:
--   The BDL26 Uniform RXTail construction uses the cleaned Error x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L92-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L92-L103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.cleanedError_x_zero (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
      (cleanedError S j) = 0 := by sorry
