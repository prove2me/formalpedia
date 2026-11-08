-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_physicalStep_parity
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.physicalStep_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:21.399436+00:00
-- url     : https://prove2.me/theorems/e4f4221a-582e-40eb-b3f7-ecc7d06c7db8
-- title:
--   Level Two History: physical Step parity
-- statement:
--   The Level Two History construction uses the physical Step parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L30-L32

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.physicalStep_parity (i : StepIndex n) :
    replacementKind (physicalStep i).val = replacementKind i.val := by sorry
