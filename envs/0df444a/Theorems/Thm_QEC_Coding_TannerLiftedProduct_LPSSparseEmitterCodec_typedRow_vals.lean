-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_typedRow_vals
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedRow_vals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:39:19.299279+00:00
-- url     : https://prove2.me/theorems/165ea949-74fd-442d-85aa-1604f8056b2f
-- title:
--   LPSSparse Emitter Codec: typed Row vals
-- statement:
--   The LPSSparse Emitter Codec construction uses the typed Row vals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L180-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L180-L184

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedRow_vals {n s:ℕ} (r:List (Fin n×Fin s)):
 typedRow n s (r.map (fun e=>(e.1.val,e.2.val)))=some r:= by sorry
