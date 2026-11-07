-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicKeptLift_mem_puncturedReedMullerCode
-- name    : QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_puncturedReedMullerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:28.263551+00:00
-- url     : https://prove2.me/theorems/4434d97a-a2fd-45ab-a5ba-a165198e1c7b
-- title:
--   Punctured Reed Muller: systematic Kept Lift mem punctured Reed Muller Code
-- statement:
--   Every retained systematic lift belongs to the punctured Reed--Muller code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L338-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L338-L348

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_puncturedReedMullerCode {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (puncturedReedMullerCode r m w).carrier := by sorry
