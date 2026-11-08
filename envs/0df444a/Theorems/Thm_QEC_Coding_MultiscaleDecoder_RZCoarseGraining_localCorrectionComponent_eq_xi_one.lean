-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_eq_xi_one
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrectionComponent_eq_xi_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:04.625199+00:00
-- url     : https://prove2.me/theorems/b8a26939-551d-4cbb-933d-cc2cd6da5f16
-- title:
--   RZCoarse Graining: local Correction Component eq xi one
-- statement:
--   The RZCoarse Graining construction uses the local Correction Component eq xi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L659-L667
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L659-L667

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrectionComponent_eq_xi_one
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    localCorrectionComponent A hcoh z sigma =
      localCorrectionComponent A hcoh z (xiSignal A sigma z 1) := by sorry
