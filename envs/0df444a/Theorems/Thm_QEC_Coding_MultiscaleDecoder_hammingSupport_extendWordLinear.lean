-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_hammingSupport_extendWordLinear
-- name    : QEC.Coding.MultiscaleDecoder.hammingSupport_extendWordLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:16:25.260648+00:00
-- url     : https://prove2.me/theorems/8f521165-5874-46b9-ae96-b8583171071b
-- title:
--   Multiscale Decoder: hamming Support extend Word Linear
-- statement:
--   The Multiscale Decoder construction uses the hamming Support extend Word Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L124-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L124-L137

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

theorem QEC.Coding.MultiscaleDecoder.hammingSupport_extendWordLinear
    {F : Type u} [Field F] [DecidableEq F] {ι : Type v} [Fintype ι]
    [DecidableEq ι]
    (Y : Finset ι) (signal : Word F (LocalRegionIndex Y)) :
    hammingSupport (extendWordLinear Y signal) =
      Finset.image Subtype.val (hammingSupport signal) := by sorry
