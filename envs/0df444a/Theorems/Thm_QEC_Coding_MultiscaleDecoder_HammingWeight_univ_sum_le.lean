-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_HammingWeight_univ_sum_le
-- name    : QEC.Coding.MultiscaleDecoder.HammingWeight_univ_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:15:41.246788+00:00
-- url     : https://prove2.me/theorems/3519cad4-9784-4cd3-8974-58b93f2d0932
-- title:
--   Multiscale Decoder: Hamming Weight univ sum le
-- statement:
--   The Multiscale Decoder construction uses the Hamming Weight univ sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L78-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L78-L84

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

theorem QEC.Coding.MultiscaleDecoder.HammingWeight_univ_sum_le
    {F : Type u} {ι : Type v} {κ : Type w}
    [AddCommGroup F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (f : κ → Word F ι) :
    HammingWeight (∑ k : κ, f k) ≤ ∑ k : κ, HammingWeight (f k) := by sorry
