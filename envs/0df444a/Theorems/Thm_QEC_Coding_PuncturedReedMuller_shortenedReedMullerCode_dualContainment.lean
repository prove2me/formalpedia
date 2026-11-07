-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dualContainment
-- name    : QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dualContainment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:49.485018+00:00
-- url     : https://prove2.me/theorems/100ee92c-ac29-4418-a871-ceabba75e4df
-- title:
--   Punctured Reed Muller: shortened Reed Muller Code dual Containment
-- statement:
--   The two shortened HH18 Reed--Muller codes satisfy CSS dual containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L613-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L613-L631

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dualContainment
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).carrier ≤
      (shortenedReedMullerCode r m w).dual.carrier := by sorry
