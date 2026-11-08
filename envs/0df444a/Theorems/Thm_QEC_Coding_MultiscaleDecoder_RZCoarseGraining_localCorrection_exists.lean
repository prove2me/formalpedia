-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrection_exists
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrection_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:26:30.336081+00:00
-- url     : https://prove2.me/theorems/24335e8a-d0bc-4e65-a319-7594f2a06077
-- title:
--   RZCoarse Graining: local Correction exists
-- statement:
--   The RZCoarse Graining construction uses the local Correction exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L237-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L237-L261

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrection_exists
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (r : D.family.Cochain2 i.succ)
    (hsupport : ∀ p, p ∉ A.coarseRegion z → r p = 0)
    (hparity : ∑ p ∈ A.coarseRegion z, r p = 0) :
    ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = r p) := by sorry
