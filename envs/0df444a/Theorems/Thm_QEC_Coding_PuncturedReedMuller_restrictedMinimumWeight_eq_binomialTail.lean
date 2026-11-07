-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedMinimumWeight_eq_binomialTail
-- name    : QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_eq_binomialTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:58.264675+00:00
-- url     : https://prove2.me/theorems/74f3b309-3d7b-48b1-9850-31ce6ec76807
-- title:
--   Punctured Reed Muller: restricted Minimum Weight eq binomial Tail
-- statement:
--   The concrete restricted nonzero Reed--Muller spectrum has exactly the
--   HH18 binomial-tail minimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1736-L1746
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L1736-L1746

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_eq_binomialTail
    {m r w : Nat} (hnoKernel : w < m - r) :
    restrictedMinimumWeight r m w = binomialTail (m - r) w := by sorry
