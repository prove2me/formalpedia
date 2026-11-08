-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLListMachine_Filter_original_output_source
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.original_output_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:32:16.932577+00:00
-- url     : https://prove2.me/theorems/9eb7d355-f68b-4047-bfff-14bcb34b2fa2
-- title:
--   Filter: original output source
-- statement:
--   Actual complete PSL-row execution, original source identity, q-only initialization or whole runtime certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLListMachine.lean#L180-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLListMachine.lean#L180-L181

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter._p2m_local_instance_e75c5360c0_157
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.original_output_source (q:ℕ) [Fact q.Prime]:
 (representatives q (lpsSLList q)).map (quotient q)=lpsPSLList q:= by sorry
