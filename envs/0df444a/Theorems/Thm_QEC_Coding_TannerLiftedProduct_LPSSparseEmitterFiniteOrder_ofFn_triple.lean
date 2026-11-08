-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_triple
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:06:09.027899+00:00
-- url     : https://prove2.me/theorems/59f54f5e-7570-4e3c-ac47-ee6c84cd0186
-- title:
--   LPSSparse Emitter Finite Order: of Fn triple
-- statement:
--   The LPSSparse Emitter Finite Order construction uses the of Fn triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L134-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L134-L142

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_triple {α:Type*} {m n k:ℕ} (f:Fin m×Fin n×Fin k→α):
 (List.ofFn fun i:Fin (m*(n*k))=>f ((lpsSparseTripleEquiv m n k).symm i))=
 (List.ofFn fun i:Fin m=>(List.ofFn fun j:Fin n=>List.ofFn fun t:Fin k=>f (i,j,t)).flatten).flatten:= by sorry
