-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_fields_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.fields_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:41.071465+00:00
-- url     : https://prove2.me/theorems/c58d62c7-c5ce-4c73-848b-2f4e7f19392a
-- title:
--   LPSSparse Emitter Codec: fields injective
-- statement:
--   The LPSSparse Emitter Codec construction uses the fields injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L56-L60

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.fields_injective:Function.Injective fields:= by sorry
