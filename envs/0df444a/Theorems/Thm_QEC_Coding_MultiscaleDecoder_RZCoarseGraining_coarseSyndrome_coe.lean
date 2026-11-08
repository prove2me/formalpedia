-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:29.134011+00:00
-- url     : https://prove2.me/theorems/57915130-0ea3-4124-befe-ca7a5415249c
-- title:
--   RZCoarse Graining: coarse Syndrome coe
-- statement:
--   The RZCoarse Graining construction uses the coarse Syndrome coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L375-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L375-L381

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) =
      topParity A sigma.1 := by sorry

attribute [defeq] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
