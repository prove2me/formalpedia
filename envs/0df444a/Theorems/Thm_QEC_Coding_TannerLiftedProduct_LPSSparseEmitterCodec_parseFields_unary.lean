-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_parseFields_unary
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.parseFields_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:36:08.365239+00:00
-- url     : https://prove2.me/theorems/d0e7642a-ee3e-4b57-b75c-9cf572955a83
-- title:
--   LPSSparse Emitter Codec: parse Fields unary
-- statement:
--   The LPSSparse Emitter Codec construction uses the parse Fields unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L151-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L151-L159

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.parseFields_unary (n a:ℕ) (w:List Bool):
 parseFields n (unary a++false::w)=(parseFields 0 w).map ((n+a)::·):= by sorry
