-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_coarse_weight
-- name    : QEC.Coding.BDL26UniformRXTail.actual_coarse_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:16:59.264319+00:00
-- url     : https://prove2.me/theorems/12fed4ff-bcc8-4057-a727-f8d583dd2631
-- title:
--   BDL26 Uniform RXTail: actual coarse weight
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual coarse weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L278-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L278-L282

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_coarse_weight (S : OddScale) (j : Nat) :
    2 * HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
      (tailIndex j).castSucc (actualConstants S j)) ≤ HammingWeight (lowerSyndrome S j).val := by sorry
