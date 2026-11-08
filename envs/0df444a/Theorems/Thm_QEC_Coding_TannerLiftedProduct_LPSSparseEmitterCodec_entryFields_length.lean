-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_entryFields_length
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:33:48.334091+00:00
-- url     : https://prove2.me/theorems/4e71f1ed-ccfc-46f0-b2c4-78d240249d97
-- title:
--   LPSSparse Emitter Codec: entry Fields length
-- statement:
--   The LPSSparse Emitter Codec construction uses the entry Fields length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L64-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L64-L67

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_length (r:Row):(entryFields r).length=2*r.length:= by sorry
