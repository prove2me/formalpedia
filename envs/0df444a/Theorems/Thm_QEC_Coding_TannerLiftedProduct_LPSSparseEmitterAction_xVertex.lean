-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterAction_xVertex
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.xVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:15:15.565654+00:00
-- url     : https://prove2.me/theorems/dd9c5b23-574c-4e36-924e-14ee5999e90d
-- title:
--   LPSSparse Emitter Action: x Vertex
-- statement:
--   The LPSSparse Emitter Action construction uses the x Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L289-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L289-L289

import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
import Definitions.Def_QEC_Coding_BitTuring_SuffixJoin
import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterRowMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction._p2m_local_instance_8f991ae56e_149
open LPSOriginalGeneratorIndexMachine

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.xVertex {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product false false v i=lpsPSLIndexMul q v i:= by sorry
