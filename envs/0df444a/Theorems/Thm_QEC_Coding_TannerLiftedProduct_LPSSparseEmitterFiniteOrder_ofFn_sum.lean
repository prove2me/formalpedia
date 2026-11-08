-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_sum
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:50.872777+00:00
-- url     : https://prove2.me/theorems/4b5df0d3-d003-4ae9-8fd8-5c40369db30f
-- title:
--   LPSSparse Emitter Finite Order: of Fn sum
-- statement:
--   The LPSSparse Emitter Finite Order construction uses the of Fn sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L111-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L111-L120

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_sum {α:Type*} {m n:ℕ} (f:Fin m⊕Fin n→α):
 (List.ofFn fun i:Fin (m+n)=>f (finSumFinEquiv.symm i))=
 (List.ofFn fun i:Fin m=>f (Sum.inl i))++(List.ofFn fun i:Fin n=>f (Sum.inr i)):= by sorry
