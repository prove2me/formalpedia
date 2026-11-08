-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_liftCorrection_map1_eq
-- name    : QEC.Coding.MultiscaleDecoder.liftCorrection_map1_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:07.421894+00:00
-- url     : https://prove2.me/theorems/3b5b7e93-e4f3-42ae-836b-28875a80c235
-- title:
--   Multiscale Decoder: lift Correction map1 eq
-- statement:
--   The original correction lift factors through its actual next selected
--   map. This equation exposes the unchanged private recursion at adjacent levels.
--   It is appended after the existing declarations to preserve their elaboration
--   order and private proof identities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1620-L1629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1620-L1629

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

theorem QEC.Coding.MultiscaleDecoder.liftCorrection_map1_eq
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (w : D.family.Correction i.castSucc) :
    liftCorrection D i.castSucc w =
      liftCorrection D i.succ ((D.selectedMap i).map1 w) := by sorry
