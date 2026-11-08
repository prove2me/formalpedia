-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_rpow_le_balancingLift
-- name    : QEC.Coding.ExpanderCodes.PK20.rpow_le_balancingLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:45.878263+00:00
-- url     : https://prove2.me/theorems/a30a8265-d8ae-4684-a8aa-d2093a8647ca
-- title:
--   PK20: rpow le balancing Lift
-- statement:
--   The PK20 construction uses the rpow le balancing Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L252-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L252-L260

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.rpow_le_balancingLift (alpha : ℝ) (q : Nat) :
    (q : ℝ) ^ balancingExponent alpha ≤ balancingLift alpha q := by sorry
