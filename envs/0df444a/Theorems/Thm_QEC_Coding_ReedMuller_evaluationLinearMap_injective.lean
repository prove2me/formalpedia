-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_evaluationLinearMap_injective
-- name    : QEC.Coding.ReedMuller.evaluationLinearMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:14.488212+00:00
-- url     : https://prove2.me/theorems/87c0eb7b-dd04-44f1-9fb4-05a7ec17aefc
-- title:
--   Reed Muller: evaluation Linear Map injective
-- statement:
--   Boolean ANF evaluation is injective, by triangular elimination on monomial support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L124-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L124-L161

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.evaluationLinearMap_injective (m r : Nat) :
    Function.Injective (evaluationLinearMap m r) := by sorry
