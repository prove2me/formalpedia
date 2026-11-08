-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXErrorTransport_q_sector_transport
-- name    : QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport.q_sector_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:03:40.690459+00:00
-- url     : https://prove2.me/theorems/83fa9b60-b263-405c-a0a0-5b5d5ebe5c4e
-- title:
--   RXError Transport: q sector transport
-- statement:
--   The RXError Transport construction uses the q sector transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXErrorTransport.lean#L144-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXErrorTransport.lean#L144-L268

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXErrorTransport
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
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport

theorem QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport.q_sector_transport
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∃ lowerCorrection : D.family.Cochain1 i.castSucc,
      ∃ lowerSyndrome : D.family.Syndrome i.castSucc,
        ∃ stabilizer : D.family.Cochain0 i.succ,
          (D.rxMap i).map1 lowerCorrection =
              error + D.family.coboundary0 i.succ stabilizer ∧
          D.family.coboundary1 i.succ
              (D.family.coboundary0 i.succ stabilizer) = 0 ∧
          (lowerSyndrome : D.family.Cochain2 i.castSucc) =
              D.family.coboundary1 i.castSucc lowerCorrection ∧
          (D.selectedMap i).map2 lowerSyndrome =
              D.family.coboundary1 i.succ error ∧
          SupportedOn A.zSector ((D.selectedMap i).map2 lowerSyndrome) := by sorry
