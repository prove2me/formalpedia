-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_binomialTail_mono_left
-- name    : QEC.Coding.PuncturedReedMuller.binomialTail_mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:46.257419+00:00
-- url     : https://prove2.me/theorems/588e764f-5f09-4054-abe9-e80d2f40306a
-- title:
--   Punctured Reed Muller: binomial Tail mono left
-- statement:
--   Increasing the ambient Boolean-cube dimension cannot decrease a fixed
--   binomial tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1477-L1487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1477-L1487

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.binomialTail_mono_left {a b w : Nat} (hab : a ≤ b) :
    binomialTail a w ≤ binomialTail b w := by sorry
