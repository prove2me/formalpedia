-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_globalCorrection_eq_input
-- name    : QEC.Coding.MultiscaleDecoder.globalCorrection_eq_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:05.564277+00:00
-- url     : https://prove2.me/theorems/27afce98-52c1-449e-8897-e9cb9641ea94
-- title:
--   Multiscale Decoder: global Correction eq input
-- statement:
--   The Multiscale Decoder construction uses the global Correction eq input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1118-L1127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1118-L1127

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

theorem QEC.Coding.MultiscaleDecoder.globalCorrection_eq_input
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth)
        (assembleCorrectionAux D S B depth (Nat.le_refl _) sigma) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by sorry
