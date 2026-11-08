-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_below_two
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.syndromeReadout_below_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:30:20.176206+00:00
-- url     : https://prove2.me/theorems/05f6f20c-0140-4e6a-9c20-bdc7a386a364
-- title:
--   Level Two History: syndrome Readout below two
-- statement:
--   The Level Two History construction uses the syndrome Readout below two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L284-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L284-L303

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.syndromeReadout_below_two (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    syndromeReadout D H i = 0 := by sorry
