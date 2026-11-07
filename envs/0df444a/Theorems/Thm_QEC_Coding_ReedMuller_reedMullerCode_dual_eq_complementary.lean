-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dual_eq_complementary
-- name    : QEC.Coding.ReedMuller.reedMullerCode_dual_eq_complementary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:32.016537+00:00
-- url     : https://prove2.me/theorems/edfc8672-6872-4720-9a04-d53dd0e9436f
-- title:
--   Reed Muller: reed Muller Code dual eq complementary
-- statement:
--   Complementary full Reed--Muller codes are exact duals below the full degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L701-L718
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L701-L718

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.reedMullerCode_dual_eq_complementary {r m : Nat}
    (hrm : r < m) :
    (reedMullerCode (m - r - 1) m).dual.carrier =
      (reedMullerCode r m).carrier := by sorry
