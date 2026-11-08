-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_liftedProductAlmostLinearDistance
-- name    : QEC.Coding.ExpanderCodes.PK20.liftedProductAlmostLinearDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:38:21.293063+00:00
-- url     : https://prove2.me/theorems/495799cd-5179-40f0-b552-5599a6da4579
-- title:
--   PK20: lifted Product Almost Linear Distance
-- statement:
--   PK20 Theorems 1--2 conditional only on PK20 Proposition 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/LiftedProductAlmostLinear.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/LiftedProductAlmostLinear.lean#L30-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
import Definitions.Def_QEC_Results_QLDPC_LiftedProductAlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20

theorem QEC.Coding.ExpanderCodes.PK20.liftedProductAlmostLinearDistance
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    LiftedProductAlmostLinearDistance := by sorry
