-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterAction_zFace
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.zFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:14:38.171278+00:00
-- url     : https://prove2.me/theorems/d2424e9c-101c-454f-9a06-71a79209b08d
-- title:
--   LPSSparse Emitter Action: z Face
-- statement:
--   The LPSSparse Emitter Action construction uses the z Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L290-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L290-L290

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

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.zFace {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product true false v i=lpsPSLIndexMul q (lpsPSLIndexInv q v) i:= by sorry
