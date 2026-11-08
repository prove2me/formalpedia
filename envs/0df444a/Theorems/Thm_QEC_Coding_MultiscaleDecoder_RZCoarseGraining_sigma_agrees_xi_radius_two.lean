-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_sigma_agrees_xi_radius_two
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sigma_agrees_xi_radius_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:13.657371+00:00
-- url     : https://prove2.me/theorems/fb0bee25-b072-4b4f-aa05-68bb6efe6e23
-- title:
--   RZCoarse Graining: sigma agrees xi radius two
-- statement:
--   The RZCoarse Graining construction uses the sigma agrees xi radius two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L581-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L581-L588

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sigma_agrees_xi_radius_two
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    SignalAgreementWithin A z 2 sigma (xiSignal A sigma z 2) := by sorry
