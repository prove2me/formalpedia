-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cx_error_cleaning_all
-- name    : QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice.cx_error_cleaning_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:42:48.82722+00:00
-- url     : https://prove2.me/theorems/d2480e04-8d6c-4ee1-9529-e7ce7df89e9f
-- title:
--   RXConstruction Contract Slice: cx error cleaning all
-- statement:
--   The RXConstruction Contract Slice construction uses the cx error cleaning all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L872-L903
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L872-L903

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a b c
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}

theorem QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice.cx_error_cleaning_all
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hcocycle : ∀ x, K.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error) = 0) :
    ∃ stabilizers : ∀ x, Word BDL26Field (X0 x),
      ∀ x, restrictWordLinear (Lx.correctionRegion x)
        (error + D.family.coboundary0 i.succ
          (∑ y : X, K.support_decomposition.cxLift0 y (stabilizers y))) = 0 := by sorry
