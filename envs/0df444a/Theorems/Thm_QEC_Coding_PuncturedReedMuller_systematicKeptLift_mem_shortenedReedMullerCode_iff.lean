-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicKeptLift_mem_shortenedReedMullerCode_iff
-- name    : QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_shortenedReedMullerCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:04:07.816721+00:00
-- url     : https://prove2.me/theorems/1eddbbdc-34b2-4b1b-be54-58cf496c5d48
-- title:
--   Punctured Reed Muller: systematic Kept Lift mem shortened Reed Muller Code iff
-- statement:
--   The systematic retained lift represents a shortened word precisely when
--   its prescribed low block is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L571-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L571-L610

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_shortenedReedMullerCode_iff {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier ↔ logical = 0 := by sorry
