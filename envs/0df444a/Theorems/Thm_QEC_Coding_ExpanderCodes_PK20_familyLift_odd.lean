-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_odd
-- name    : QEC.Coding.ExpanderCodes.PK20.familyLift_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:33.296008+00:00
-- url     : https://prove2.me/theorems/88025a32-20d6-4ec2-a88a-6a20c5e95f57
-- title:
--   PK20: family Lift odd
-- statement:
--   The PK20 construction uses the family Lift odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L959-L961
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L959-L961

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.familyLift_odd (w radiusDenominator B : Nat) :
    Odd (familyLift w radiusDenominator B) := by sorry
