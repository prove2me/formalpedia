-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_HammingWeight_finset_sum_le
-- name    : QEC.Coding.MultiscaleDecoder.HammingWeight_finset_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:16:17.434611+00:00
-- url     : https://prove2.me/theorems/8f1fd7fa-77a8-4915-831f-02702e73c72a
-- title:
--   Multiscale Decoder: Hamming Weight finset sum le
-- statement:
--   The Multiscale Decoder construction uses the Hamming Weight finset sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L64-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L64-L76

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

theorem QEC.Coding.MultiscaleDecoder.HammingWeight_finset_sum_le
    {F : Type u} {ι : Type v} {κ : Type w}
    [AddCommGroup F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Fintype κ]
    (s : Finset κ) (f : κ → Word F ι) :
    HammingWeight (∑ k ∈ s, f k) ≤ ∑ k ∈ s, HammingWeight (f k) := by sorry
