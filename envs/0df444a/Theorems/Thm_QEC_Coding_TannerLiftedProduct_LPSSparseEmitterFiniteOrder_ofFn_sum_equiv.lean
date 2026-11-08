-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_sum_equiv
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_sum_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:05:39.004425+00:00
-- url     : https://prove2.me/theorems/ff64323b-50d7-450c-b67e-b7e18ed3cb8d
-- title:
--   LPSSparse Emitter Finite Order: of Fn sum equiv
-- statement:
--   The LPSSparse Emitter Finite Order construction uses the of Fn sum equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L129-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L129-L133

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_sum_equiv {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A⊕B→α):
 (List.ofFn fun i:Fin (m+n)=>f (((Equiv.sumCongr ea eb).trans finSumFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>f (Sum.inl (ea.symm i)))++(List.ofFn fun i:Fin n=>f (Sum.inr (eb.symm i))):= by sorry
