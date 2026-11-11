-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_q_supported
-- name    : QEC.Coding.BDL26UniformRXTail.cleanedError_q_supported
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:09:24.391668+00:00
-- url     : https://prove2.me/theorems/c32466d0-8747-451c-a220-7e25bfdcd5ca
-- title:
--   BDL26 Uniform RXTail: cleaned Error q supported
-- statement:
--   The BDL26 Uniform RXTail construction uses the cleaned Error q supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L151-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L151-L160

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.cleanedError_q_supported (S : OddScale) (j : Nat) :
    SupportedOn (tailData S j).qCorrectionSector (cleanedError S j) := by sorry
