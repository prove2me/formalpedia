-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_gt
-- name    : QEC.Coding.ExpanderCodes.PK20.familyLift_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:41:06.343718+00:00
-- url     : https://prove2.me/theorems/e453c113-71cc-4f7c-8a3b-886e3a108281
-- title:
--   PK20: family Lift gt
-- statement:
--   The PK20 construction uses the family Lift gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L963-L972
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L963-L972

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.familyLift_gt (w radiusDenominator B : Nat) :
    B < familyLift w radiusDenominator B := by sorry
