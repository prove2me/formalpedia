-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_HammingWeight_add_of_disjoint
-- name    : QEC.Coding.MultiscaleDecoder.HammingWeight_add_of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:16:11.745199+00:00
-- url     : https://prove2.me/theorems/65503be2-3d44-4cdd-b102-1acb221d16ee
-- title:
--   Multiscale Decoder: Hamming Weight add of disjoint
-- statement:
--   The Multiscale Decoder construction uses the Hamming Weight add of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L52-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean#L52-L62

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

theorem QEC.Coding.MultiscaleDecoder.HammingWeight_add_of_disjoint
    {F : Type u} {ι : Type v} [AddGroup F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι]
    (x y : Word F ι)
    (hxy : Disjoint (hammingSupport x) (hammingSupport y)) :
    HammingWeight (x + y) = HammingWeight x + HammingWeight y := by sorry
