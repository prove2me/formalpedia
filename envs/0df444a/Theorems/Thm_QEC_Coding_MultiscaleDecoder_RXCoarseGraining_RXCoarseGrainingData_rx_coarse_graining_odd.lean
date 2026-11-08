-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_graining_odd
-- name    : QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:33.060047+00:00
-- url     : https://prove2.me/theorems/56c492f8-4e76-496a-b5b4-837e589d0d26
-- title:
--   RXCoarse Graining Data: rx coarse graining odd
-- statement:
--   The RXCoarse Graining Data construction uses the rx coarse graining odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L2192-L2538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L2192-L2538

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)

theorem QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
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
