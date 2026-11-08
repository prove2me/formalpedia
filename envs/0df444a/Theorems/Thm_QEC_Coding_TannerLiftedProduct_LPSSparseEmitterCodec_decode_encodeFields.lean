-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encodeFields
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decode_encodeFields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:33:38.630566+00:00
-- url     : https://prove2.me/theorems/08b529c6-345f-41b8-8c68-b52385c222f6
-- title:
--   LPSSparse Emitter Codec: decode encode Fields
-- statement:
--   The LPSSparse Emitter Codec construction uses the decode encode Fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L51-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L51-L55

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decode_encodeFields (rs:List Row):decodeFields (fields rs)=some rs:= by sorry
