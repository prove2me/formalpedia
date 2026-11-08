-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_coarse_graining_even
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_coarse_graining_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:46:44.203344+00:00
-- url     : https://prove2.me/theorems/314e6352-1de3-40e8-80e5-7ce1a2df4985
-- title:
--   RZCoarse Graining: rz coarse graining even
-- statement:
--   The RZCoarse Graining construction uses the rz coarse graining even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L736-L766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L736-L766

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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_coarse_graining_even
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : UpperSyndrome D i) :
    ∃ sigma' : CoarseSyndrome D i,
      ∃ correction : D.family.Cochain1 i.succ,
        correction = correctionFromSyndrome A hcoh sigma.1 ∧
        (sigma : D.family.Cochain2 i.succ) =
          D.family.coboundary1 i.succ correction +
            (D.selectedMap i).map2 sigma' ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 2 sigma.1 tau.1 →
          (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
            (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 1 sigma.1 tau.1 →
          localCorrectionComponent A hcoh z sigma.1 =
            localCorrectionComponent A hcoh z tau.1) := by sorry
