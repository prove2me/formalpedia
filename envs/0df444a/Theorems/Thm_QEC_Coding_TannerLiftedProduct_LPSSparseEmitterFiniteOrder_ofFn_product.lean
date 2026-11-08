-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_product
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:33.949426+00:00
-- url     : https://prove2.me/theorems/d2f5bfa5-8fd5-42ce-b002-ffe2fcda63d4
-- title:
--   LPSSparse Emitter Finite Order: of Fn product
-- statement:
--   The LPSSparse Emitter Finite Order construction uses the of Fn product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L97-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L97-L110

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_product {α:Type*} {m n:ℕ} (f:Fin m×Fin n→α):
 (List.ofFn fun i:Fin (m*n)=>f (finProdFinEquiv.symm i))=
 (List.ofFn fun i:Fin m=>List.ofFn fun j:Fin n=>f (i,j)).flatten:= by sorry
