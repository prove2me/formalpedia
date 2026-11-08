-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_two
-- name    : QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:23:43.392134+00:00
-- url     : https://prove2.me/theorems/76ca9396-7482-4daf-9c83-95a0ecf3d21e
-- title:
--   Multiscale Decoder: build Correction History two
-- statement:
--   Exact three-entry expansion, retaining both step outputs and the actual base.
--   This shape lemma avoids unfolding the recursive implementation at a large
--   concrete family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L766-L786
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L766-L786

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_two
    {A0 A1 A2 : LevelIndex 2 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 2 A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex 2)) :
    buildCorrectionHistory D S B sigma =
      [.step 1 (S.step 1 sigma),
       .step 0 (S.step 0 (S.step 1 sigma).coarse),
       .base { input := (S.step 0 (S.step 1 sigma).coarse).coarse
               correction := B.decode (S.step 0 (S.step 1 sigma).coarse).coarse
               relation := (B.rightInverse (S.step 0 (S.step 1 sigma).coarse).coarse).symm }] := by sorry
