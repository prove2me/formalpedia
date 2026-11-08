-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_extend_restrict_sum_eq_mask
-- name    : QEC.Coding.MultiscaleDecoder.extend_restrict_sum_eq_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:16:01.308117+00:00
-- url     : https://prove2.me/theorems/71ff4cd3-2bef-434c-baac-1eaacc7d4ab3
-- title:
--   Multiscale Decoder: extend restrict sum eq mask
-- statement:
--   The Multiscale Decoder construction uses the extend restrict sum eq mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L266-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L266-L304

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

theorem QEC.Coding.MultiscaleDecoder.extend_restrict_sum_eq_mask
    {F : Type u} {ι : Type v} {κ : Type w}
    [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (regions : κ → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (regions a) (regions b))
    (signal : Word F ι) :
    (∑ k : κ, extendWordLinear (regions k)
      (restrictWordLinear (regions k) signal)) =
      maskWord (Finset.biUnion Finset.univ regions) signal := by sorry
