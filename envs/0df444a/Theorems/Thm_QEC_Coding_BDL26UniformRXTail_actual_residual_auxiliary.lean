-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_residual_auxiliary
-- name    : QEC.Coding.BDL26UniformRXTail.actual_residual_auxiliary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:12:44.707901+00:00
-- url     : https://prove2.me/theorems/86651906-d26b-4e1c-bfda-129fff99a759
-- title:
--   BDL26 Uniform RXTail: actual residual auxiliary
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual residual auxiliary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L348-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L348-L353

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_residual_auxiliary (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (tailIndex j).succ)
    (hp : p ∉ (tailData S j).induced.zSector) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val p = 0 := by sorry
