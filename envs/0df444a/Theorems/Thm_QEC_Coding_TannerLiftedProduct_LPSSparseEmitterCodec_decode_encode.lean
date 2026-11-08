-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encode
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decode_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:36:45.675935+00:00
-- url     : https://prove2.me/theorems/0cca9c01-5c8e-4bac-9df4-9c61a82d2bc9
-- title:
--   LPSSparse Emitter Codec: decode encode
-- statement:
--   The LPSSparse Emitter Codec construction uses the decode encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L166-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L166-L167

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decode_encode (rs:List Row):decode (encode rs)=some rs:= by sorry
