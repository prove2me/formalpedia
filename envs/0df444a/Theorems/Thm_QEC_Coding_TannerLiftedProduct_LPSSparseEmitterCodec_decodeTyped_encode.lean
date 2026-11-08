-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decodeTyped_encode
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeTyped_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:07:14.547031+00:00
-- url     : https://prove2.me/theorems/d6e4a275-4edf-4e0c-8c0e-7313b454d770
-- title:
--   LPSSparse Emitter Codec: decode Typed encode
-- statement:
--   The LPSSparse Emitter Codec construction uses the decode Typed encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L191-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L191-L193

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeTyped_encode {n s:ℕ} (rs:List (List (Fin n×Fin s))):
 decodeTyped n s (encode (numeric n s rs))=some rs:= by sorry
