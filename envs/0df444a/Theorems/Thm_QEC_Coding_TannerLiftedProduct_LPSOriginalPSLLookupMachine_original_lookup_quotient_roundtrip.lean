-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_original_lookup_quotient_roundtrip
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_lookup_quotient_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:51:13.984589+00:00
-- url     : https://prove2.me/theorems/d4d46822-086a-47c7-a568-fcbf0ce00e20
-- title:
--   LPSOriginal PSLLookup Machine: original lookup quotient roundtrip
-- statement:
--   Lookup after original quotient indexing recovers that exact quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L224-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L224-L226

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine._p2m_local_instance_eed6317f64_203

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_lookup_quotient_roundtrip (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 quotient q (representative q ((lpsPSLEnumerationEquiv q).symm (quotient q A)))=quotient q A:= by sorry
