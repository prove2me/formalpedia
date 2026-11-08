-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_invariant_radius_two
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_invariant_radius_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:57.342921+00:00
-- url     : https://prove2.me/theorems/d41bd129-a047-45ad-8915-96f00dfd5110
-- title:
--   RZCoarse Graining: coarse Syndrome invariant radius two
-- statement:
--   The RZCoarse Graining construction uses the coarse Syndrome invariant radius two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L726-L734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L726-L734

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_invariant_radius_two
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (z : C2 i.castSucc)
    (sigma tau : UpperSyndrome D i)
    (hAgree : SignalAgreementWithin A z 2 sigma.1 tau.1) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
      (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z := by sorry
