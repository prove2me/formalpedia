-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_card_squarefree
-- name    : QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_card_squarefree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:11.11327+00:00
-- url     : https://prove2.me/theorems/431975e5-e4c4-41a2-8b34-21462bdeeef9
-- title:
--   Reed Muller: reed Muller Code dimension eq card squarefree
-- statement:
--   The Reed--Muller code dimension is the number of squarefree ANF monomials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L205-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L205-L211

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_card_squarefree (r m : Nat) :
    Dimension (reedMullerCode r m) = Fintype.card (SquarefreeMonomial m r) := by sorry
