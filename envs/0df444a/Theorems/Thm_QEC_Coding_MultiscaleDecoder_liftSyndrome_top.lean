-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftSyndrome_top
-- name    : QEC.Coding.MultiscaleDecoder.liftSyndrome_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:22:31.187691+00:00
-- url     : https://prove2.me/theorems/34d7ca0c-474d-455f-b805-2f316fa61b56
-- title:
--   Multiscale Decoder: lift Syndrome top
-- statement:
--   The Multiscale Decoder construction uses the lift Syndrome top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L514-L518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L514-L518

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.liftSyndrome_top
    (D : BDL26DecoderData depth C0 C1 C2)
    (s : D.family.Cochain2 (TopIndex depth)) :
    liftSyndrome D (TopIndex depth) s = s := by sorry
