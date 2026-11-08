-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_product_equiv
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_product_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:35:53.865852+00:00
-- url     : https://prove2.me/theorems/a57a879d-7708-4cdc-a67a-ddd0e8133e10
-- title:
--   LPSSparse Emitter Finite Order: of Fn product equiv
-- statement:
--   The LPSSparse Emitter Finite Order construction uses the of Fn product equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L124-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L124-L128

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_product_equiv {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A×B→α):
 (List.ofFn fun i:Fin (m*n)=>f (((Equiv.prodCongr ea eb).trans finProdFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>List.ofFn fun j:Fin n=>f (ea.symm i,eb.symm j)).flatten:= by sorry
