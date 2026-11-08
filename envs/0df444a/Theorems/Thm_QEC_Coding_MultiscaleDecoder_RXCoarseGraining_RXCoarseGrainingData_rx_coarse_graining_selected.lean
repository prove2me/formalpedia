-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_graining_selected
-- name    : QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:12:54.228404+00:00
-- url     : https://prove2.me/theorems/a7f3b98b-0afc-4d59-b175-325cbb039d9d
-- title:
--   RXCoarse Graining Data: rx coarse graining selected
-- statement:
--   The full canonical reduction, with actual selected-map compatibility in
--   place of an unrelated physical parity label. All conclusions are derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L2578-L2923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L2578-L2923

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_selected
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hSelected : D.selectedMap i = D.rxMap i)
    (sigma : D.family.Syndrome i.succ) :
    ∃ sigma' : D.family.Syndrome i.castSucc,
      ∃ correction : D.family.Correction i.succ,
        (sigma' : D.family.Cochain2 i.castSucc) =
            rxCoarseWord A (sigma : D.family.Cochain2 i.succ) ∧
        correction = rxCorrectionTotal A (sigma : D.family.Cochain2 i.succ) ∧
        (sigma : D.family.Cochain2 i.succ) =
            D.family.coboundary1 i.succ correction +
              (D.selectedMap i).map2 sigma' ∧
        2 * HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) / 2 ∧
        SupportedOn A.zSector ((D.selectedMap i).map2 sigma') ∧
        (∀ p ∈ A.xSector, ((D.selectedMap i).map2 sigma') p = 0) ∧
        (∀ p ∈ A.qSector, ((D.selectedMap i).map2 sigma') p = 0) := by sorry
