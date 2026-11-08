-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localResidual_supported
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localResidual_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:26:38.694496+00:00
-- url     : https://prove2.me/theorems/15a74f97-af0f-4ba2-8142-a7c012242255
-- title:
--   RZCoarse Graining: local Residual supported
-- statement:
--   The RZCoarse Graining construction uses the local Residual supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L269-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L269-L277

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localResidual_supported
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∀ p, p ∉ A.coarseRegion z → localResidual A z sigma p = 0 := by sorry
