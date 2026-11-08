-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_outsideMaskWord_add_maskWord
-- name    : QEC.Coding.MultiscaleDecoder.outsideMaskWord_add_maskWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:15:33.338065+00:00
-- url     : https://prove2.me/theorems/578adc72-bf2c-4270-bcf6-a2017d041814
-- title:
--   Multiscale Decoder: outside Mask Word add mask Word
-- statement:
--   The Multiscale Decoder construction uses the outside Mask Word add mask Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L117-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L117-L122

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

theorem QEC.Coding.MultiscaleDecoder.outsideMaskWord_add_maskWord
    {F : Type u} [AddGroup F] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (signal : Word F ι) :
    outsideMaskWord Y signal + maskWord Y signal = signal := by sorry
