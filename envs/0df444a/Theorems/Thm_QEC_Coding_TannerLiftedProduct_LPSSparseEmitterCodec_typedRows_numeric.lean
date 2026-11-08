-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_typedRows_numeric
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedRows_numeric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:36:30.330138+00:00
-- url     : https://prove2.me/theorems/90799ed7-c19e-4a68-8bde-4b167d6d81de
-- title:
--   LPSSparse Emitter Codec: typed Rows numeric
-- statement:
--   The LPSSparse Emitter Codec construction uses the typed Rows numeric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L185-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L185-L188

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedRows_numeric {n s:ℕ} (rs:List (List (Fin n×Fin s))):typedRows n s (numeric n s rs)=some rs:= by sorry
