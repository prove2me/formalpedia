-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_physical
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.syndromeReadout_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:25:00.780196+00:00
-- url     : https://prove2.me/theorems/e175eea1-3616-459b-95f2-4ab2f8398a8c
-- title:
--   Level Two History: syndrome Readout physical
-- statement:
--   Physical reindexing preserves the exact sum of matching input snapshots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L233-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L233-L252

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.syndromeReadout_physical
    (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex n) :
    syndromeReadout D H (physicalLevel i) = historyInputReadout (suffixData D) H i := by sorry
