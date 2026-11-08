-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_encode_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.encode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:23:29.951895+00:00
-- url     : https://prove2.me/theorems/62cf3d62-a549-411a-95f6-d952e3f97f02
-- title:
--   LPSSparse Emitter Codec: encode injective
-- statement:
--   The LPSSparse Emitter Codec construction uses the encode injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L61-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L61-L63

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.encode_injective:Function.Injective encode:= by sorry
