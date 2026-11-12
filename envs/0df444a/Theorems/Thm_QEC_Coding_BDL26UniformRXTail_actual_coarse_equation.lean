-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_coarse_equation
-- name    : QEC.Coding.BDL26UniformRXTail.actual_coarse_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:14:59.218671+00:00
-- url     : https://prove2.me/theorems/de2f0b2b-b444-4fec-b73d-1b6f51ab057d
-- title:
--   BDL26 Uniform RXTail: actual coarse equation
-- statement:
--   No hypotheses beyond S,j: all selected local equations have been discharged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L272-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L272-L276

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_coarse_equation (S : OddScale) (j : Nat) :
    (rxStepOutput S (2 * j + 4) (tailIndex j) (tailIndex_even j) (lowerSyndrome S j)).coarse.val =
      (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j) := by sorry
