-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_entryFields_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:05:41.57659+00:00
-- url     : https://prove2.me/theorems/ef177bf8-8446-4f85-96cf-86d108ef967e
-- title:
--   LPSSparse Emitter Codec: entry Fields injective
-- statement:
--   The LPSSparse Emitter Codec construction uses the entry Fields injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L86-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L86-L93

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_injective:Function.Injective entryFields:= by sorry
