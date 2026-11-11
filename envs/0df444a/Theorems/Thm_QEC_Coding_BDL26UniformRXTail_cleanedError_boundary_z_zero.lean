-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_boundary_z_zero
-- name    : QEC.Coding.BDL26UniformRXTail.cleanedError_boundary_z_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:13:41.501834+00:00
-- url     : https://prove2.me/theorems/e01e227d-add3-483d-8d33-046000f86698
-- title:
--   BDL26 Uniform RXTail: cleaned Error boundary z zero
-- statement:
--   The BDL26 Uniform RXTail construction uses the cleaned Error boundary z zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L315-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L315-L323

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.cleanedError_boundary_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (cleanedError S j)
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by sorry
