-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_base_readout
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_base_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:44.490883+00:00
-- url     : https://prove2.me/theorems/c09cb47f-e157-47c0-9240-8981bae73f36
-- title:
--   Level Two History: stopped History base readout
-- statement:
--   The physical C2 snapshot agrees with the actual recursively selected input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L255-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L255-L262

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_base_readout
    (D : BDL26DecoderData (n + 2) C0 C1 C2) (S : AboveTwoSteps D)
    (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    syndromeReadout D (stoppedHistory D S B sigma) (physicalLevel (0 : LevelIndex n)) =
      (terminalInput (suffixData D) (suffixSteps D S) sigma).val := by sorry
