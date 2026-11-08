-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_coboundary_liftCorrection
-- name    : QEC.Coding.MultiscaleDecoder.coboundary_liftCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:14.952318+00:00
-- url     : https://prove2.me/theorems/146bcc09-0292-424b-9c49-7ff2a824eac5
-- title:
--   Multiscale Decoder: coboundary lift Correction
-- statement:
--   The Multiscale Decoder construction uses the coboundary lift Correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L520-L561
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L520-L561

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

theorem QEC.Coding.MultiscaleDecoder.coboundary_liftCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) :
    D.family.coboundary1 (TopIndex depth) (liftCorrection D i f) =
      liftSyndrome D i (D.family.coboundary1 i f) := by sorry
