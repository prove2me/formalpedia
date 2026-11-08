-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseParity_invariant_radius_two
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseParity_invariant_radius_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:52.007864+00:00
-- url     : https://prove2.me/theorems/c9683484-05f7-4df4-9d14-25fc7d8dae2a
-- title:
--   RZCoarse Graining: coarse Parity invariant radius two
-- statement:
--   The RZCoarse Graining construction uses the coarse Parity invariant radius two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L590-L599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L590-L599

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseParity_invariant_radius_two
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (sigma tau : D.family.Cochain2 i.succ)
    (hAgree : SignalAgreementWithin A z 2 sigma tau) :
    topParity A sigma z = topParity A tau z := by sorry
