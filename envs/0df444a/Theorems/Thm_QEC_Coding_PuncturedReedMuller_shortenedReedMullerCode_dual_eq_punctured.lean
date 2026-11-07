-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured
-- name    : QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:50.195818+00:00
-- url     : https://prove2.me/theorems/6c48113a-692b-4eff-a263-18ef6a013018
-- title:
--   Punctured Reed Muller: shortened Reed Muller Code dual eq punctured
-- statement:
--   Under the punctured shortened Reed--Muller admissibility window, the dual
--   of the complementary shortened code is exactly the punctured low-degree code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L729-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L729-L739

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by sorry
