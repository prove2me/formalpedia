-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_sum_choose
-- name    : QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_sum_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:50.071997+00:00
-- url     : https://prove2.me/theorems/bc357dda-75db-4db8-856c-b40097352e0e
-- title:
--   Reed Muller: reed Muller Code dimension eq sum choose
-- statement:
--   Raw source form of the Reed--Muller dimension identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L221-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L221-L224

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_sum_choose (r m : Nat) :
    Dimension (reedMullerCode r m) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by sorry
