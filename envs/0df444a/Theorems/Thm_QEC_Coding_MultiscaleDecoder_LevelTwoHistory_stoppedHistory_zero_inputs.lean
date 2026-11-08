-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_zero_inputs
-- name    : QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_zero_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:29:29.783652+00:00
-- url     : https://prove2.me/theorems/052a1fc2-1eef-48b8-8d3e-4aa97ad0a7b2
-- title:
--   Level Two History: stopped History zero inputs
-- statement:
--   A zero-preserving physical decoder retains zero syndrome snapshots in its
--   fixed C2-stopped history. Corrections and components are not erased.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L147-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean#L147-L153

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_zero_inputs (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (hz : ∀ i hi sigma, sigma.val = 0 → (S.step i hi sigma).coarse.val = 0)
    (sigma : D.family.Syndrome (TopIndex (n + 2))) (hs : sigma.val = 0) :
    ∀ e ∈ stoppedHistory D S B sigma, e.inputSyndrome.2.val = 0 := by sorry
