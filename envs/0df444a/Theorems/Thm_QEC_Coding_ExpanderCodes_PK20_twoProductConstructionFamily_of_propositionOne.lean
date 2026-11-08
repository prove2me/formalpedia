-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twoProductConstructionFamily_of_propositionOne
-- name    : QEC.Coding.ExpanderCodes.PK20.twoProductConstructionFamily_of_propositionOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:18:30.685905+00:00
-- url     : https://prove2.me/theorems/b4d723b2-d587-46dd-8ddf-665e65cd21b2
-- title:
--   PK20: two Product Construction Family of proposition One
-- statement:
--   Proposition 1 constructs every finite member in the two-product family;
--   there is no independent assumption of asymptotically good classical codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L300-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L300-L359

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.twoProductConstructionFamily_of_propositionOne
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    TwoProductConstructionFamily := by sorry
