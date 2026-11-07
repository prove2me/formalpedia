-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_evaluation_mem_reedMullerCode
-- name    : QEC.Coding.ReedMuller.evaluation_mem_reedMullerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:56.372459+00:00
-- url     : https://prove2.me/theorems/25d8d090-0b8e-4bdb-9b4c-e2bafe4991a1
-- title:
--   Reed Muller: evaluation mem reed Muller Code
-- statement:
--   Every concrete polynomial evaluation belongs to the Reed--Muller code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L96-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L96-L99

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.evaluation_mem_reedMullerCode {r m : Nat}
    (polynomial : ANFPolynomial m r) :
    evaluationLinearMap m r polynomial ∈ (reedMullerCode r m).carrier := by sorry
