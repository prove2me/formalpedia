-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualQWord_boundary
-- name    : QEC.Coding.BDL26UniformRXTail.actualQWord_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T07:29:22.458168+00:00
-- url     : https://prove2.me/theorems/710c7595-fac6-4844-8a4d-ca12289a232b
-- title:
--   BDL26 Uniform RXTail: actual QWord boundary
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual QWord boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L132-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L132-L139

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actualQWord_boundary (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    (tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q) =
      restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).syndromeRegion q)
        (rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val) := by sorry
