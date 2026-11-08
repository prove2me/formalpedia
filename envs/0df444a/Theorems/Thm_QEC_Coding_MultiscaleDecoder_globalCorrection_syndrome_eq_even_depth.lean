-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_globalCorrection_syndrome_eq_even_depth
-- name    : QEC.Coding.MultiscaleDecoder.globalCorrection_syndrome_eq_even_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:26:42.508031+00:00
-- url     : https://prove2.me/theorems/8c5db538-d5c3-4e03-a9be-19387cfa3357
-- title:
--   Multiscale Decoder: global Correction syndrome eq even depth
-- statement:
--   The Multiscale Decoder construction uses the global Correction syndrome eq even depth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1213-L1227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1213-L1227

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

theorem QEC.Coding.MultiscaleDecoder.globalCorrection_syndrome_eq_even_depth
    {k : Nat}
    {C0 : LevelIndex (2 * k) → Type u}
    {C1 : LevelIndex (2 * k) → Type u}
    {C2 : LevelIndex (2 * k) → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
    [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData (2 * k) C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex (2 * k))) :
    D.family.coboundary1 (TopIndex (2 * k))
        (globalCorrection D S B sigma) =
      (sigma : D.family.Cochain2 (TopIndex (2 * k))) := by sorry
