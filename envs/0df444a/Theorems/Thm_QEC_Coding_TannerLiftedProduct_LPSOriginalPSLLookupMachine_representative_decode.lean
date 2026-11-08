-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_representative_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.representative_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:44:00.309205+00:00
-- url     : https://prove2.me/theorems/0cb1f7bc-d922-422d-9106-4c68d24dd985
-- title:
--   LPSOriginal PSLLookup Machine: representative decode
-- statement:
--   The selected original representative quotient is exactly the source enumeration value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L213-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L213-L218

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine._p2m_local_instance_eed6317f64_203

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.representative_decode (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 quotient q (representative q i)=(lpsPSLEnumerationEquiv q) i:= by sorry
