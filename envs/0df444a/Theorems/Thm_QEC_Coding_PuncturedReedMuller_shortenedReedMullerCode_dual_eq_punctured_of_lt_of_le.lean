-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
-- name    : QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:12.979554+00:00
-- url     : https://prove2.me/theorems/9a6262d9-6099-45e4-80de-c0934cc74a7e
-- title:
--   Punctured Reed Muller: shortened Reed Muller Code dual eq punctured of lt of le
-- statement:
--   Shortening the complementary full Reed--Muller code is exactly dual to
--   puncturing the degree-`r` code when both complementary parameters are in
--   range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L636-L725
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L636-L725

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
    {w r m : Nat} (hrm : r < m) (hcomplement : w ≤ m - r - 1) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by sorry
