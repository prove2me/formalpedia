-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterAction_xFace
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.xFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:13:39.434191+00:00
-- url     : https://prove2.me/theorems/863bd1f5-5947-48c5-81e2-b15d3b80c39d
-- title:
--   LPSSparse Emitter Action: x Face
-- statement:
--   The LPSSparse Emitter Action construction uses the x Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L288-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L288-L288

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

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.xFace {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product true true v i=lpsPSLIndexMul q i (lpsPSLIndexInv q v):= by sorry
