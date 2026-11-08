-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_decode_output
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decode_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:45:58.903413+00:00
-- url     : https://prove2.me/theorems/3e7c48cd-b183-47f5-b0a2-f89528f3bab4
-- title:
--   LPSSparse Emitter Source: decode output
-- statement:
--   The LPSSparse Emitter Source construction uses the decode output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L274-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterSourceMachine.lean#L274-L277

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
open LPSSparseEmitterRow

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decode_output {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeFields (LPSSparseEmitterCodec.fields (checks a g t h h'))=some (checks a g t h h'):= by sorry
