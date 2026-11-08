-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_entryFields_sum
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:24:07.947181+00:00
-- url     : https://prove2.me/theorems/cb5cf4f3-663c-4336-b2d3-643255b35430
-- title:
--   LPSSparse Emitter Codec: entry Fields sum
-- statement:
--   The LPSSparse Emitter Codec construction uses the entry Fields sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L74-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterCodec.lean#L74-L77

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_sum (r:Row):(entryFields r).sum=(r.map fun e=>e.1+e.2).sum:= by sorry
