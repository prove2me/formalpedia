-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_syndrome
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:30:20.499003+00:00
-- url     : https://prove2.me/theorems/e52559e5-b2fa-4d7f-beed-09baaa038c17
-- title:
--   Level Two History: stopped History syndrome
-- statement:
--   The actual lifted sum of this same history has the supplied top syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L306-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L306-L311

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_syndrome (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    D.family.coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (suffixData D) (stoppedHistory D S B sigma)) = sigma.val := by sorry
