-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_le_puncturedReedMullerCode
-- name    : QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_le_puncturedReedMullerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:46.614767+00:00
-- url     : https://prove2.me/theorems/2ccacbe3-d687-457c-8ceb-9e6ba628dd88
-- title:
--   Punctured Reed Muller: shortened Reed Muller Code le punctured Reed Muller Code
-- statement:
--   Shortening produces a subcode of the corresponding punctured code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L127-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L127-L134

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_le_puncturedReedMullerCode
    (r m w : Nat) :
    (shortenedReedMullerCode r m w).carrier ≤
      (puncturedReedMullerCode r m w).carrier := by sorry
