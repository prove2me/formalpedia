-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftSyndrome_map2_eq
-- name    : QEC.Coding.MultiscaleDecoder.liftSyndrome_map2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:33.510505+00:00
-- url     : https://prove2.me/theorems/1974786b-44a9-4c29-ba17-fe87636007c4
-- title:
--   Multiscale Decoder: lift Syndrome map2 eq
-- statement:
--   The Multiscale Decoder construction uses the lift Syndrome map2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L586-L596
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L586-L596

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

theorem QEC.Coding.MultiscaleDecoder.liftSyndrome_map2_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (s : D.family.Cochain2 i.castSucc) :
    liftSyndrome D i.castSucc s =
      liftSyndrome D i.succ ((D.selectedMap i).map2 s) := by sorry
