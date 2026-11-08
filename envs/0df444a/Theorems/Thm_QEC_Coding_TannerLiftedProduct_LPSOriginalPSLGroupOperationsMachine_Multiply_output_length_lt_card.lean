-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLGroupOperationsMachine_Multiply_output_length_lt_card
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply.output_length_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:12:26.755261+00:00
-- url     : https://prove2.me/theorems/fe1c8b54-fa67-47ed-821c-9a7d18e08c70
-- title:
--   Multiply: output length lt card
-- statement:
--   The emitted original finite index is strictly below the genuine PSL cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLGroupOperationsMachine.lean#L482-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLGroupOperationsMachine.lean#L482-L486

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLIndexMachine_output_length_lt_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply._p2m_local_instance_7fc643cdab_248

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply.output_length_lt_card (a:Input):(output a).length<Fintype.card PSL(2,ZMod a.1.val):= by sorry
