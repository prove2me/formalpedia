-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstAlmostLinearFamily_of_propositionOne
-- name    : QEC.Coding.ExpanderCodes.PK20.firstAlmostLinearFamily_of_propositionOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:23:44.373302+00:00
-- url     : https://prove2.me/theorems/8158fe88-1edf-4a3e-8a59-60a6f378bbde
-- title:
--   PK20: first Almost Linear Family of proposition One
-- statement:
--   Proposition 1 alone supplies the complete first PK20 family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L996-L1037
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L996-L1037

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.firstAlmostLinearFamily_of_propositionOne
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    FirstAlmostLinearFamily := by sorry
