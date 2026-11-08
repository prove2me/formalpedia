-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_output_length_le
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.output_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:51:39.481449+00:00
-- url     : https://prove2.me/theorems/53d82494-62cc-478d-b4eb-df16a4281ede
-- title:
--   LPSOriginal PSLLookup Machine: output length le
-- statement:
--   Four bounded canonical coordinates bound actual output length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L298-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L298-L309

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine._p2m_local_instance_eed6317f64_203

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.output_length_le (a:Input):(output a).length≤4*a.1.val+3:= by sorry
