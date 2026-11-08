-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_correction_boundary_eq_sumResidual
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.correction_boundary_eq_sumResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:48.761519+00:00
-- url     : https://prove2.me/theorems/29edde9f-e9de-4030-b229-0d14c8562cfa
-- title:
--   RZCoarse Graining: correction boundary eq sum Residual
-- statement:
--   The RZCoarse Graining construction uses the correction boundary eq sum Residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L418-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L418-L431

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.correction_boundary_eq_sumResidual
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ) :
    D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma) =
      ∑ z, localResidual A z sigma := by sorry
