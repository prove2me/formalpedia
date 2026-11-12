-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_local_q_translate_one
-- name    : QEC.Coding.BDL26UniformRXTail.local_q_translate_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:33:57.870813+00:00
-- url     : https://prove2.me/theorems/4a616dd0-cf8c-4fca-a0e4-2b38946c3488
-- title:
--   BDL26 Uniform RXTail: local q translate one
-- statement:
--   Constant translation is real freedom of the local CQ equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L12-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L12-L17

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformRXTail.local_q_translate_one
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (g : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => g v + 1) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) g := by sorry
