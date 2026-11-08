-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_typedEntry_vals
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedEntry_vals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:36:53.0332+00:00
-- url     : https://prove2.me/theorems/6764becb-c9be-4ee9-9f28-10e0cd59718f
-- title:
--   LPSSparse Emitter Codec: typed Entry vals
-- statement:
--   The LPSSparse Emitter Codec construction uses the typed Entry vals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L178-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L178-L179

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.typedEntry_vals {n s:ℕ} (e:Fin n×Fin s):typedEntry n s (e.1.val,e.2.val)=some e:= by sorry
