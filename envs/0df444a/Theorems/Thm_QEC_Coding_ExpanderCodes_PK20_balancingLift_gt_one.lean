-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_balancingLift_gt_one
-- name    : QEC.Coding.ExpanderCodes.PK20.balancingLift_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:45.771401+00:00
-- url     : https://prove2.me/theorems/800dbeac-0311-4353-ac4d-66eeb57ad279
-- title:
--   PK20: balancing Lift gt one
-- statement:
--   The PK20 construction uses the balancing Lift gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L247-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L247-L250

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.balancingLift_gt_one (alpha : ℝ) (q : Nat) :
    1 < balancingLift alpha q := by sorry
