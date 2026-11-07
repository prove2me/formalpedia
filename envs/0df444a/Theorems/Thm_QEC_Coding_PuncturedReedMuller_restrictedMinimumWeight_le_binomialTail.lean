-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedMinimumWeight_le_binomialTail
-- name    : QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_binomialTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:29.630222+00:00
-- url     : https://prove2.me/theorems/ee7a7b9a-4426-4c75-889a-a3f6dece5e65
-- title:
--   Punctured Reed Muller: restricted Minimum Weight le binomial Tail
-- statement:
--   The actual restricted Reed--Muller minimum is at most the HH18 binomial
--   tail, witnessed by the concrete ANF word above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1020-L1028
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1020-L1028

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_binomialTail
    {m r w : Nat} (hrm : r ≤ m) :
    restrictedMinimumWeight r m w ≤ binomialTail (m - r) w := by sorry
