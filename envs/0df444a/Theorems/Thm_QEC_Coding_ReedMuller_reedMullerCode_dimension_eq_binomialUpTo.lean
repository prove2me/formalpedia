-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_binomialUpTo
-- name    : QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_binomialUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:26.546492+00:00
-- url     : https://prove2.me/theorems/c0d727a7-0cb9-406c-b6ad-9012746cf393
-- title:
--   Reed Muller: reed Muller Code dimension eq binomial Up To
-- statement:
--   The Reed--Muller code dimension is the source-stated cumulative binomial
--   sum through its degree bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L215-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L215-L218

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_binomialUpTo (r m : Nat) :
    Dimension (reedMullerCode r m) = binomialUpTo m r := by sorry
