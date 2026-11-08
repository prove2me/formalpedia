-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_entryPhysicalLevel_bounds
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.entryPhysicalLevel_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:40.983089+00:00
-- url     : https://prove2.me/theorems/e3297a3e-eb2d-4d65-8c87-57fc96ce93a5
-- title:
--   Level Two History: entry Physical Level bounds
-- statement:
--   The Level Two History construction uses the entry Physical Level bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L195-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L195-L203

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.entryPhysicalLevel_bounds (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) :
    2 ≤ entryPhysicalLevel D e ∧ entryPhysicalLevel D e ≤ n + 2 := by sorry
