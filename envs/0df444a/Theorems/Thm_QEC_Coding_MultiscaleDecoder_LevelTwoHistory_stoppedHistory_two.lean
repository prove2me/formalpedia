-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_two
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:40.679664+00:00
-- url     : https://prove2.me/theorems/f0251f3d-6917-4103-880f-cf6ac89bb923
-- title:
--   Level Two History: stopped History two
-- statement:
--   Physical C4-to-C2 expansion before instantiating a concrete finite family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L170-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L170-L183

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_two
    {A0 A1 A2 : LevelIndex 4 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 4 A0 A1 A2) (S : AboveTwoSteps (n := 2) D)
    (B : AuditedBaseDecoder (suffixData (n := 2) D))
    (sigma : D.family.Syndrome (TopIndex 4)) :
    stoppedHistory (n := 2) D S B sigma =
      [.step 1 (suffixOutput D 1 (S.step 3 (by decide) sigma)),
       .step 0 (suffixOutput D 0 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse)),
       .base { input := (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               correction := B.decode (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               relation := (B.rightInverse
                 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse).symm }] := by sorry
