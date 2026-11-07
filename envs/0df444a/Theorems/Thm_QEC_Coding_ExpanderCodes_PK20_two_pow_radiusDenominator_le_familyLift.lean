-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_two_pow_radiusDenominator_le_familyLift
-- name    : QEC.Coding.ExpanderCodes.PK20.two_pow_radiusDenominator_le_familyLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:40.948549+00:00
-- url     : https://prove2.me/theorems/000eccdf-0559-46f6-ab5e-6c32085a77dd
-- title:
--   PK20: two pow radius Denominator le family Lift
-- statement:
--   The PK20 construction uses the two pow radius Denominator le family Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L974-L983
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L974-L983

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.two_pow_radiusDenominator_le_familyLift
    (w radiusDenominator B : Nat) :
    2 ^ radiusDenominator ≤ familyLift w radiusDenominator B := by sorry
