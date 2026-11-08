-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterAction_zVertex
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.zVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:16:33.832309+00:00
-- url     : https://prove2.me/theorems/766fc9d0-3e90-4c4d-a3b8-a64b382d1f59
-- title:
--   LPSSparse Emitter Action: z Vertex
-- statement:
--   The LPSSparse Emitter Action construction uses the z Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L291-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean#L291-L291

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

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.zVertex {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product false true v i=lpsPSLIndexMul q i v:= by sorry
