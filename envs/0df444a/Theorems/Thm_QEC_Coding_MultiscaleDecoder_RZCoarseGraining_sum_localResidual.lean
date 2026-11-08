-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_sum_localResidual
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sum_localResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:26:10.800574+00:00
-- url     : https://prove2.me/theorems/dd46cbd9-a330-4e0d-b2d8-d1e67c29915d
-- title:
--   RZCoarse Graining: sum local Residual
-- statement:
--   The RZCoarse Graining construction uses the sum local Residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L402-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L402-L416

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sum_localResidual
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    (∑ z, localResidual A z sigma) =
      sigma + (D.rzMap i).map2 (topParity A sigma) := by sorry
