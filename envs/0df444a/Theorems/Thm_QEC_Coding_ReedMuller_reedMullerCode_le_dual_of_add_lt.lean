-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_le_dual_of_add_lt
-- name    : QEC.Coding.ReedMuller.reedMullerCode_le_dual_of_add_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:22.744236+00:00
-- url     : https://prove2.me/theorems/320f160c-9380-4b47-855d-31a5a2accd50
-- title:
--   Reed Muller: reed Muller Code le dual of add lt
-- statement:
--   Reed--Muller codes whose degrees sum below m satisfy dual containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L332-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L332-L341

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.reedMullerCode_le_dual_of_add_lt {m r s : Nat}
    (hdegree : r + s < m) :
    (reedMullerCode s m).carrier ≤ (reedMullerCode r m).dual.carrier := by sorry
