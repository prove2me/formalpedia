-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_suffixOutput_supports
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.suffixOutput_supports
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:39.396411+00:00
-- url     : https://prove2.me/theorems/1f374157-6b58-4d70-a749-ff2c86d1c2c9
-- title:
--   Level Two History: suffix Output supports
-- statement:
--   The Level Two History construction uses the suffix Output supports property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L112-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L112-L114

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.suffixOutput_supports (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).componentSupports = O.componentSupports := by sorry
