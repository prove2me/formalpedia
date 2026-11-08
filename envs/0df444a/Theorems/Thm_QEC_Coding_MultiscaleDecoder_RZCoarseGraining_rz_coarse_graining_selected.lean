-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_coarse_graining_selected
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_coarse_graining_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:46:42.53321+00:00
-- url     : https://prove2.me/theorems/45a41e97-9622-41d1-85db-31f2ec75d32a
-- title:
--   RZCoarse Graining: rz coarse graining selected
-- statement:
--   The same full canonical RZ reduction on a literal local replacement edge.
--   No syndrome relation, local exactness or target conclusion is assumed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L809-L839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L809-L839

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.RZCoarseGraining
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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_coarse_graining_selected
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hselected : D.selectedMap i = D.rzMap i)
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
