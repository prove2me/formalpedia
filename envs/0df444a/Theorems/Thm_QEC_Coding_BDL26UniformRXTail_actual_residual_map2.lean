-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_residual_map2
-- name    : QEC.Coding.BDL26UniformRXTail.actual_residual_map2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T06:54:43.972728+00:00
-- url     : https://prove2.me/theorems/fd8a163e-82d3-4380-91ce-94edcc25e69b
-- title:
--   BDL26 Uniform RXTail: actual residual map2
-- statement:
--   The complete residual, including all auxiliary sectors, is the actual selected map2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L256-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L256-L269

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_residual_map2 (S : OddScale) (j : Nat) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val =
      ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).map2
        ((indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j)) := by sorry
