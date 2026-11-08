-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftSyndrome_add
-- name    : QEC.Coding.MultiscaleDecoder.liftSyndrome_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:22:47.053292+00:00
-- url     : https://prove2.me/theorems/d1ad9a93-5610-4289-94d2-2222f39426f0
-- title:
--   Multiscale Decoder: lift Syndrome add
-- statement:
--   The Multiscale Decoder construction uses the lift Syndrome add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L563-L584
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L563-L584

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

theorem QEC.Coding.MultiscaleDecoder.liftSyndrome_add
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (a b : D.family.Cochain2 i) :
    liftSyndrome D i (a + b) =
      liftSyndrome D i a + liftSyndrome D i b := by sorry
